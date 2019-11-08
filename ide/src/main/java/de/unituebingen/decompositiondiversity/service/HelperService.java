/**
 * 
 */
package de.unituebingen.decompositiondiversity.service;

import org.springframework.ui.Model;

import de.unituebingen.decompositiondiversity.message.request.Request;
import de.unituebingen.decompositiondiversity.message.response.GetCasesResponse;
import de.unituebingen.decompositiondiversity.message.response.ServerResponse;

/**
 * @author Fayez Abu Alia
 *
 */
public interface HelperService {
	public ServerResponse<GetCasesResponse> perform(Request req, String source, Model model);
}
