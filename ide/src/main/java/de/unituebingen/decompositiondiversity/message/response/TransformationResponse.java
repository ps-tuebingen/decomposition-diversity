/**
 * 
 */
package de.unituebingen.decompositiondiversity.message.response;

/**
 * The response of the transform service.
 * 
 * @author Fayez Abu Alia
 *
 */
public class TransformationResponse {
	/**
	 * The transformed Program.
	 */
	private String source;
	/**
	 * The source code before transformation.
	 */
	private String oldSource;
	/**
	 * Error.
	 */
	private String error;
	
	public String getSource() {
		return source;
	}

	public void setSource(String source) {
		this.source = source;
	}

	public String getOldSource() {
		return oldSource;
	}

	public void setOldSource(String oldSource) {
		this.oldSource = oldSource;
	}

	public String getError() {
		return error;
	}

	public void setError(String error) {
		this.error = error;
	}
	
}
