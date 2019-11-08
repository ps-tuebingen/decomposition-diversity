/**
 * 
 */
package de.unituebingen.decompositiondiversity.message.response;

import java.util.ArrayList;
import java.util.Map;

/**
 * The response of the get cases.
 * 
 * @author Fayez Abu Alia
 */
public class GetCasesResponse {
	/**
	 * Signature of transformed function.
	 */
//	private String signature;
	/**
	 * All co-/cases.
	 */
//	private ArrayList<String> body;
	private String body;
	/**
	 * Error.
	 */
	private String error;
	
	private Map<String, String> consAndDesMap;
	
//	public String getSignature() {
//		return signature;
//	}
//
//	public void setSignature(String signature) {
//		this.signature = signature;
//	}

//	public ArrayList<String> getBody() {
//		return body;
//	}
//
//	public void setBody(ArrayList<String> body) {
//		this.body = body;
//	}
	public String getBody() {
		return body;
	}

	public void setBody(String body) {
		this.body = body;
	}
	public String getError() {
		return error;
	}

	public void setError(String error) {
		this.error = error;
	}
	
	public Map<String, String> getconsAndDesMap() {
		return consAndDesMap;
	}

	public void setConsAndDesMap(Map<String, String> consAndDesMap) {
		this.consAndDesMap = consAndDesMap;
	}
}
