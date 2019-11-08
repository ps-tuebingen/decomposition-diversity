/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler;

import java.io.IOException;

import de.unituebingen.decompositiondiversity.message.response.CompilerResponse;

/**
 * @author Fayez Abu Alia
 *
 */
public interface ICompiler {
	public abstract CompilerResponse compile(String prog) throws IOException;
}
