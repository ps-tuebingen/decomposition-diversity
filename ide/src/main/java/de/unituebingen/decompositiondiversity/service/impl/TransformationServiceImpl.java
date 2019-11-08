package de.unituebingen.decompositiondiversity.service.impl;

import java.io.IOException;

import org.json.JSONObject;

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
public abstract class TransformationServiceImpl implements CompilerService {
	protected String serviceName;
	
	@Override
	public ServerResponse<String> perform(JSONObject paramTrans) {
		
		ServerResponse<String> result = new ServerResponse<>();
		
		try {
			ObjectMapper mapper = new ObjectMapper();
			
			ConnectionService connSer = new ConnectionServiceImpl();
			
			result = connSer.getResponse(serviceName,paramTrans);
			
			if(result.getStatus().equals(Constants.SUCCESS)) {
				JSONObject ppParams = new JSONObject();
				Object progToPrint = mapper.readValue(result.getData().toString(), Object.class);
				ppParams.put(Constants.COQ_PROGRAM, progToPrint);
				Config.config.setProgram(progToPrint);
				Object config = mapper.readValue(Config.config.toJSON().toString(), Object.class);
				ppParams.put(Constants.CONFIG, config);
				
				CompilerService prettyPrint = new PrettyPrintProgramServiceImpl();
				ServerResponse<String> prettyProg = prettyPrint.perform(ppParams);
				
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
