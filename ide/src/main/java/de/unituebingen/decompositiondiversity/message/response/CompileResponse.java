/**
 * 
 */
package de.unituebingen.decompositiondiversity.message.response;

import java.util.ArrayList;
import java.util.Map;

/**
 * The response of the compile service.
 * 
 * @author Fayez Abu Alia
 */
public class CompileResponse {
	/**
	 * List of data names.
	 */
	private ArrayList<String> data;
	/**
	 * List of codata names.
	 */
	private ArrayList<String> codata;
	/**
	 * compile errors.
	 */
	private String errors;
	
	private Map<String, String> consAndDesMap;
	
	private int numOfErrors;
	
	public ArrayList<String> getData() {
		return data;
	}

	public void setData(ArrayList<String> data) {
		this.data = data;
	}

	public ArrayList<String> getCodata() {
		return codata;
	}

	public void setCodata(ArrayList<String> codata) {
		this.codata = codata;
	}

	public String getErrors() {
		return errors;
	}

	public void setErrors(String errors) {
		this.errors = errors;
	}

	public Map<String, String> getconsAndDesMap() {
		return consAndDesMap;
	}

	public void setConsAndDesMap(Map<String, String> consAndDesMap) {
		this.consAndDesMap = consAndDesMap;
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
