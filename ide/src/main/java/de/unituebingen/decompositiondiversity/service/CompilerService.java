package de.unituebingen.decompositiondiversity.service;

import org.json.JSONObject;

import de.unituebingen.decompositiondiversity.message.response.ServerResponse;

/**
 * 
 * @author Fayez Abu Alia
 *
 */
public interface CompilerService {
	public ServerResponse<String> perform(JSONObject param);
}
