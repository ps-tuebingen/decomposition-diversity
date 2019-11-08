/**
 * 
 */
package de.unituebingen.decompositiondiversity.service.impl;

import java.io.IOException;
import java.util.ArrayList;

import org.json.JSONObject;
import org.springframework.stereotype.Service;

import com.fasterxml.jackson.core.JsonParseException;
import com.fasterxml.jackson.databind.JsonMappingException;
import com.fasterxml.jackson.databind.ObjectMapper;

import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchFuction;
import de.unituebingen.decompositiondiversity.compiler.environment.Environment;
import de.unituebingen.decompositiondiversity.helper.Constants;
import de.unituebingen.decompositiondiversity.message.request.AddRequest;
import de.unituebingen.decompositiondiversity.message.request.Request;
import de.unituebingen.decompositiondiversity.message.response.CompilerResponse;
import de.unituebingen.decompositiondiversity.message.response.ServerResponse;
import de.unituebingen.decompositiondiversity.service.CompilerService;
import de.unituebingen.decompositiondiversity.service.LocalCompilerService;
import de.unituebingen.decompositiondiversity.service.RefactoringService;

/**
 * @author Fayez Abu Alia
 *
 */
@Service
public class AddConstructorOrDestructorServiceImp implements RefactoringService {

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.service.RefactorinService#perform(de.unituebingen.decompositiondiversity.model.RefactoringParams)
	 */
	@Override
	public ServerResponse<String> perform(Request request, Environment env, Object program) {
		AddRequest params = (AddRequest) request;
		String type = params.getType(); // Either "constructor" or "destructor"
		String sig  = params.getName(); // What is entered in the freeform field
		String body = params.getBody();
                String prog = params.getSource(); // The actual source code

                // Compute the name of the Xtor to be added
		String name;
		if(sig.contains("(")) {
                    name = sig.substring(0, sig.indexOf("("));
		} else {
                    name = sig;
		}



		ObjectMapper mapper = new ObjectMapper();
		JSONObject param = new JSONObject();
		ServerResponse<String> response = new ServerResponse<>();

		try {
			LocalCompilerService comp = new CompileServiceImpl();

                        CompilerService lastTrans = type.equals("constructor")
                            ? new ConstructorizeServiceImpl()
                            : new DestructorizeServiceImpl();

                        //Compute the strings "typename" and "fun"
                        String typename = "";
                        String fun = "";

			if(type.equals("constructor")) {
				int start = prog.indexOf("gfun " + name);
				int idx   = prog.indexOf("=", start);
                                fun = prog.substring(start, idx+1);
				typename = env.getFunction(name).getReturnType();

			} else {
                                typename = ((MatchFuction) env.getFunction(name)).getReceiverType();
				int start = prog.indexOf("cfun " + typename + ":" + name);
				int idx = prog.indexOf("=", start);
                                fun = prog.substring(start, idx+1);
			}

			String nProg = prog.replace(fun, "").concat(body);

			param.remove(Constants.COQ_PROGRAM);
			param.remove(Constants.CONFIG);

			CompilerResponse compRes2 = comp.compile(nProg);
			if(compRes2.getNumOfErrors()>0) {
				return new ServerResponse<String>(compRes2.getStatus(), compRes2.getResult());
			}
			Object progFinal = mapper.readValue(compRes2.getResult(), Object.class);
			param.put(Constants.COQ_PROGRAM,progFinal);
			param.put(Constants.TYPENAME,typename);

			response = lastTrans.perform(param);

		} catch (JsonParseException e) {
			response.setStatus(Constants.ERROR);
			response.setData(e.getMessage());
			e.printStackTrace();
		} catch (JsonMappingException e) {
			response.setStatus(Constants.ERROR);
			response.setData(e.getMessage());
			e.printStackTrace();
		} catch (IOException e) {
			response.setStatus(Constants.ERROR);
			response.setData(e.getMessage());
			e.printStackTrace();
		}


		return response;
	}

}
