package de.unituebingen.decompositiondiversity.service.impl;

import java.io.IOException;

import org.json.JSONObject;
import org.springframework.stereotype.Service;

import com.fasterxml.jackson.core.JsonParseException;
import com.fasterxml.jackson.databind.JsonMappingException;
import com.fasterxml.jackson.databind.ObjectMapper;

import de.unituebingen.decompositiondiversity.helper.Config;
import de.unituebingen.decompositiondiversity.helper.Constants;
import de.unituebingen.decompositiondiversity.message.response.ServerResponse;
import de.unituebingen.decompositiondiversity.service.CompilerService;
import de.unituebingen.decompositiondiversity.service.ConnectionService;
/**
 * 
 * @author Fayez Abu Alia
 *
 */
@Service
public class EvaluateExpressionServiceImpl implements CompilerService {

	@Override
	public ServerResponse<String> perform(JSONObject param) {
		CompilerService parseExpr = new ParseExpressionServiceImpl();
		// parsed Expression
		ServerResponse<String> pExpr = parseExpr.perform(param);

		if (pExpr.getStatus().equals(Constants.ERROR))
			return pExpr;

		param.remove(Constants.COQ_EXPR);

		ServerResponse<String> result = new ServerResponse<>();

		ObjectMapper mapper = new ObjectMapper();
		try {
			Object exprJson = mapper.readValue(pExpr.getData().toString(), Object.class);
			param.put(Constants.COQ_EXPR, exprJson);

			ConnectionService connSer = new ConnectionServiceImpl();

			result = connSer.getResponse("onestepEval", param);

			if (result.getStatus().equals(Constants.SUCCESS)) {
				param.remove(Constants.COQ_PROGRAM);
				param.remove(Constants.COQ_EXPR);

				Object expression = mapper.readValue(result.getData().toString(), Object.class);

				param.put("expression", expression);
				
//				Object config = mapper.readValue(Config.config.toJSON().toString(), Object.class);
//				param.put(Constants.CONFIG, config);

				CompilerService prettyPrint = new PrettyPrintExpressionServiceImpl();
				ServerResponse<String> prettyProg = prettyPrint.perform(param);

				return prettyProg;
			}
		} catch (JsonParseException e) {
			e.printStackTrace();
		} catch (JsonMappingException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}

		return result;
	}

}
