/**
 * 
 */
package de.unituebingen.decompositiondiversity.service;

import de.unituebingen.decompositiondiversity.compiler.environment.Environment;
import de.unituebingen.decompositiondiversity.message.request.AutoCompleteRequest;
import de.unituebingen.decompositiondiversity.message.response.ServerResponse;

/**
 * @author Fayez Abu Alia
 *
 */
public interface AutoCompleteService {
	public ServerResponse<String> autoComplete(AutoCompleteRequest params, Environment env);
}
