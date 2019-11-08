/**
 * 
 */
package de.unituebingen.decompositiondiversity.service.impl;

import java.io.IOException;

import org.json.JSONObject;
import org.springframework.stereotype.Service;

import com.fasterxml.jackson.core.JsonParseException;
import com.fasterxml.jackson.databind.JsonMappingException;
import com.fasterxml.jackson.databind.ObjectMapper;

import de.unituebingen.decompositiondiversity.compiler.ast.Constructor;
import de.unituebingen.decompositiondiversity.compiler.ast.ConstructorOrDestructor;
import de.unituebingen.decompositiondiversity.compiler.ast.function.CoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.Function;
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
public class AddParameterServiceImp implements RefactoringService {

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.service.RefactoringService#perform(de.unituebingen.decompositiondiversity.message.request.Request, de.unituebingen.decompositiondiversity.compiler.environment.Environment, java.lang.Object)
	 */
	@Override
	public ServerResponse<String> perform(Request request, Environment env, Object program) {
		AddRequest params = (AddRequest) request;
		String type = params.getType();
		String name = params.getName();
		String body = params.getBody();
		
		ObjectMapper mapper = new ObjectMapper();
		JSONObject param = new JSONObject();
		ServerResponse<String> response = new ServerResponse<>();
		
		try {
			
			String prog = params.getSource();
			
			LocalCompilerService comp = new CompileServiceImpl();
			
			int idx = 0;
			int start = 0;
			String typename = "";
			CompilerService lastTrans = null;
			Function fun1 = env.getFunction(name);
			if(fun1 instanceof CoMatchFunction) {
				
				start = prog.indexOf("generator function "+name);
				idx = getEndIDX("generator", prog,start);
				lastTrans = new ConstructorizeServiceImpl();
				
				typename = env.getFunction(name).getReturnType();
			}else {
				typename = ((MatchFuction) env.getFunction(name)).getReceiverType();
				start = prog.indexOf("consumer function "+typename+":"+name);
				idx = getEndIDX("consumer", prog,start);
				lastTrans = new DestructorizeServiceImpl();
			}
			
			
			String fun = prog.substring(start, idx);

			String nProg = prog.replace(fun, "\n").concat(body);
			System.out.println(nProg);
			param.remove(Constants.COQ_PROGRAM);
			param.remove(Constants.CONFIG);
			
			CompilerResponse compRes2 = comp.compile(nProg);
			if(compRes2.getStatus().equals(Constants.ERROR)) {
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
	
	private int getEndIDX(String kw, String prog, int startIdx) {
		int endIdx = prog.indexOf(kw, startIdx + 1);

		if (endIdx == -1) {
			String[] kWords = { "consumer","generator", "data", "codata", "function" };
			for (String k : kWords) {
				
				if(k.equals(kw))
					continue;
				
				endIdx = prog.indexOf(k, startIdx);
				if(k.equals("function") && endIdx<(startIdx+18)) {
					endIdx = -1;
					continue;
				}
				if (endIdx != -1)
					return endIdx;
			}
			if (endIdx == -1)
				endIdx = prog.length();
		}

		return endIdx;
	}
}
