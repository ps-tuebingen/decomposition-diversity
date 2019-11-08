/**
 * 
 */
package de.unituebingen.decompositiondiversity.service;

import de.unituebingen.decompositiondiversity.compiler.environment.Environment;
import de.unituebingen.decompositiondiversity.message.request.Request;
import de.unituebingen.decompositiondiversity.message.response.ServerResponse;

/**
 * @author Fayez Abu Alia
 *
 */
public interface RefactoringService {
	public ServerResponse<String> perform(Request params, Environment env, Object program);
}
