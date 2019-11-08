/**
 * 
 */
package de.unituebingen.decompositiondiversity.service.impl;


import org.json.JSONObject;

import de.unituebingen.decompositiondiversity.message.response.ServerResponse;
import de.unituebingen.decompositiondiversity.service.CompilerService;
import de.unituebingen.decompositiondiversity.service.ConnectionService;

/**
 * @author Fayez Abu Alia
 *
 */
public abstract class PrettyPrintServiceImpl implements CompilerService {
	
	protected String serviceName;
	
	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.service.CompilerService#perform(org.json.JSONObject)
	 */
	@Override
	public ServerResponse<String> perform(JSONObject param) {
		ConnectionService conn = new ConnectionServiceImpl();
		ServerResponse<String> response = conn.getResponse(serviceName, param);
		return response;
	}

}
