/**
 * 
 */
package de.unituebingen.decompositiondiversity.message.response;

import de.unituebingen.decompositiondiversity.compiler.environment.Environment;

/**
 * @author Fayez Abu Alia
 *
 */
public class CompilerResponse {
	private String status;
	private String result;
	private String warnings;
	private Environment env;
	private int numOfErrors;
	public String getStatus() {
		return status;
	}
	public void setStatus(String status) {
		this.status = status;
	}
	public String getResult() {
		return result;
	}
	public void setResult(String result) {
		this.result = result;
	}
	/**
	 * @return the errors
	 */
	public String getWarnings() {
		return warnings;
	}
	/**
	 * @param errors the errors to set
	 */
	public void setWarnings(String warnings) {
		this.warnings = warnings;
	}
	public Environment getEnv() {
		return env;
	}
	public void setEnv(Environment env) {
		this.env = env;
	}
	/**
	 * @return the numOfErrors
	 */
	public int getNumOfErrors() {
		return numOfErrors;
	}
	/**
	 * @param numOfErrors the numOfErrors to set
	 */
	public void setNumOfErrors(int numOfErrors) {
		this.numOfErrors = numOfErrors;
	}
	
	
}
