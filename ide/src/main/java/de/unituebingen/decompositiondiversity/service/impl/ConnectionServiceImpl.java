package de.unituebingen.decompositiondiversity.service.impl;

import org.json.JSONObject;
import org.kurento.jsonrpc.client.JsonRpcClientWebSocket;
import org.springframework.stereotype.Service;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.google.gson.JsonElement;

import de.unituebingen.decompositiondiversity.helper.Constants;
import de.unituebingen.decompositiondiversity.message.response.ServerResponse;
import de.unituebingen.decompositiondiversity.service.ConnectionService;

/**
 * 
 * @author Fayez Abu Alia
 *
 */
@Service
public class ConnectionServiceImpl implements ConnectionService {
	@Override
	public ServerResponse<String> getResponse(String methodeName, JSONObject params) {
		String result = "";
		ServerResponse<String> finalResponse = new ServerResponse<>();
		JsonRpcClientWebSocket client = new JsonRpcClientWebSocket(Constants.apiAddress);
		try {

			ObjectMapper mapper = new ObjectMapper();
			Object p = mapper.readValue(params.toString(), Object.class);
			JsonElement response = client.sendRequest(methodeName, p);
			client.close();

			result = response.toString();
			finalResponse.setStatus(Constants.SUCCESS);
			finalResponse.setData(result);
			
			System.out.println("RESULT = " + result);
		} catch (org.kurento.jsonrpc.JsonRpcErrorException e) {
			e.printStackTrace();
			System.out.println("{error: " + e.getMessage() + "}");
			finalResponse.setStatus(Constants.ERROR);
            //final JSONObject error = new JSONObject(e.getMessage());
            //final String msg = error.getString("error");
            //finalResponse.setData(msg);
            finalResponse.setData(e.getMessage());
			//finalResponse.setData("The input is probably already a value (or there is a bug)");
		} catch (Exception e) {
			e.printStackTrace();
			System.out.println("{error: " + e.getMessage() + "}");
			finalResponse.setStatus(Constants.ERROR);
//			finalResponse.setData(e.getMessage());
			finalResponse.setData("A problem occurred while connecting to DecompositionDiversity API");
		}

		return finalResponse;
	}
}
