/**
 * 
 */
package de.unituebingen.decompositiondiversity.service.impl;

import java.io.IOException;

import org.json.JSONArray;
import org.json.JSONObject;
import org.springframework.stereotype.Service;

import com.fasterxml.jackson.databind.ObjectMapper;

import de.unituebingen.decompositiondiversity.compiler.ast.Program;
import de.unituebingen.decompositiondiversity.compiler.environment.Environment;
import de.unituebingen.decompositiondiversity.compiler.json.JSONGenerator;
import de.unituebingen.decompositiondiversity.compiler.parser.exception.RefactoringNotAvaliable;
import de.unituebingen.decompositiondiversity.helper.ASTWorker;
import de.unituebingen.decompositiondiversity.helper.Config;
import de.unituebingen.decompositiondiversity.helper.Constants;
import de.unituebingen.decompositiondiversity.message.request.ExtractFunctionRequest;
import de.unituebingen.decompositiondiversity.message.request.Request;
import de.unituebingen.decompositiondiversity.message.response.ServerResponse;
import de.unituebingen.decompositiondiversity.service.CompilerService;
import de.unituebingen.decompositiondiversity.service.RefactoringService;

/**
 * @author Fayez Abu Alia
 *
 */
@Service
public class ExtractFunctionServiceImp implements RefactoringService {

	/**
	 * Extracts generator/consumer function from local co-/match.
	 * 
	 * @param request the client request
	 * @return 
	 */
	@Override
	public ServerResponse<String> perform(Request request, Environment env, Object program) {
		ExtractFunctionRequest params = (ExtractFunctionRequest) request;
		
		ASTWorker astGen = new ASTWorker();
		
		try {
			Program ast = astGen.generator(params.getSource());
			
			String localName = params.getName();
			String type = params.getType();
			
			Program afterReplace = null;
			
			afterReplace = astGen.extractFunc(type,localName,ast,env);
			
			JSONGenerator jsonGen = new JSONGenerator(afterReplace);
			JSONArray jj = jsonGen.getJson();
			
			ObjectMapper mapper = new ObjectMapper();
			
			JSONObject param = new JSONObject();
			param.put(Constants.COQ_PROGRAM, jj);
			Config.config.setProgram(jj);
			Object config = mapper.readValue(Config.config.toJSON().toString(), Object.class);
			param.put(Constants.CONFIG, config);
			
			CompilerService prettyPrinter = new PrettyPrintProgramServiceImpl();
			
			return prettyPrinter.perform(param);
			
		} catch (IOException e) {
			e.printStackTrace();
			return new ServerResponse<String>(Constants.ERROR, e.getMessage());
		} catch (RefactoringNotAvaliable e) {
			e.printStackTrace();
			return new ServerResponse<String>(Constants.ERROR, e.getMessage());
		}
		
	}

}
