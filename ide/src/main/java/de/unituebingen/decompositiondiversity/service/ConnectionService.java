package de.unituebingen.decompositiondiversity.service;


import org.json.JSONObject;

import de.unituebingen.decompositiondiversity.message.response.ServerResponse;

/**
 * 
 * @author Fayez Abu Alia
 *
 */
public interface ConnectionService {
	
	public ServerResponse<String> getResponse(String methodeName,JSONObject params);

}
