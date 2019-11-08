/**
 * 
 */
package de.unituebingen.decompositiondiversity.service;

import java.io.IOException;

import de.unituebingen.decompositiondiversity.message.response.CompilerResponse;

/**
 * @author Fayez Abu Alia
 *
 */
public interface LocalCompilerService {
	public CompilerResponse compile(String prog) throws IOException;
}
