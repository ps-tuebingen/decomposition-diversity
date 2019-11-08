/**
 * 
 */
package de.unituebingen.decompositiondiversity.message.request;

/**
 * Compile request consists of source code that should 
 * be compiled.
 * 
 * @author Fayez Abu Alia
 *
 */
public class CompileRequest implements Request {
	/**
	 * The source code to be compiled.
	 */
	private String source;

	public String getSource() {
		return source;
	}

	public void setSource(String source) {
		this.source = source;
	}

}
