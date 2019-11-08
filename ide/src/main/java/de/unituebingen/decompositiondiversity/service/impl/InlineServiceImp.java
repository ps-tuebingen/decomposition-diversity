/**
 * 
 */
package de.unituebingen.decompositiondiversity.service.impl;

import org.json.JSONArray;
import org.json.JSONObject;

import com.fasterxml.jackson.databind.ObjectMapper;

import de.unituebingen.decompositiondiversity.compiler.ast.Program;
import de.unituebingen.decompositiondiversity.compiler.environment.Environment;
import de.unituebingen.decompositiondiversity.compiler.json.JSONGenerator;
import de.unituebingen.decompositiondiversity.helper.ASTWorker;
import de.unituebingen.decompositiondiversity.helper.Config;
import de.unituebingen.decompositiondiversity.helper.Constants;
import de.unituebingen.decompositiondiversity.message.request.InlineRequest;
import de.unituebingen.decompositiondiversity.message.request.Request;
import de.unituebingen.decompositiondiversity.message.response.ServerResponse;
import de.unituebingen.decompositiondiversity.service.CompilerService;
import de.unituebingen.decompositiondiversity.service.RefactoringService;

/**
 * @author Fayez Abu Alia
 *
 */
public class InlineServiceImp implements RefactoringService {

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.service.RefactoringService#perform(de.unituebingen.decompositiondiversity.message.request.Request, de.unituebingen.decompositiondiversity.environment.Environment, java.lang.Object)
	 */
	@Override
	public ServerResponse<String> perform(Request params, Environment env, Object program) {
		InlineRequest req = (InlineRequest) params;
		
		ASTWorker astGen = new ASTWorker();
		
		try {
			Program ast = astGen.generator(req.getSource());
			
			String name = req.getName();
			
			Program afterInline = astGen.inlineFunc(name, ast, env);
			
			JSONGenerator jsonGen = new JSONGenerator(afterInline);
			JSONArray jj = jsonGen.getJson();
			
			ObjectMapper mapper = new ObjectMapper();
			
			JSONObject param = new JSONObject();
			param.put(Constants.COQ_PROGRAM, jj);
			Config.config.setProgram(jj);
			Object config = mapper.readValue(Config.config.toJSON().toString(), Object.class);
			param.put(Constants.CONFIG, config);
			
			CompilerService prettyPrinter = new PrettyPrintProgramServiceImpl();
			
			return prettyPrinter.perform(param);
		} catch (Exception e) {
			e.printStackTrace();
			return new ServerResponse<String>(Constants.ERROR, e.getMessage());
		}
	}

}
