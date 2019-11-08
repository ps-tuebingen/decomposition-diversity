/**
 * 
 */
package de.unituebingen.decompositiondiversity.message.request;

import com.fasterxml.jackson.annotation.JsonProperty;

/**
 * Get co-/cases request.
 *  
 * @author Fayez Abu Alia
 */
public class GetBodyRequest implements Request{
	/**
	 * Constructor/destructor signature
	 */
	private String Signature;
	
	/**
	 * The type name its co-/cases will be 
	 * returned
	 */
	private String typename;
	
	/**
	 * "constructor" or "destructor"
	 */
	private String type;
	/**
	 * Add new Parameter
	 */
	@JsonProperty
	private boolean addParams;
	
	/**
	 * @return the signature
	 */
	public String getSignature() {
		return Signature;
	}

	/**
	 * @param signature the signature to set
	 */
	public void setSignature(String signature) {
		Signature = signature;
	}
	
	public String getType() {
		return type;
	}

	public void setType(String type) {
		this.type = type;
	}

	public boolean isParam() {
		return addParams;
	}

	public void setParam(boolean isParam) {
		this.addParams = isParam;
	}

	/**
	 * @return the typename
	 */
	public String getTypename() {
		return typename;
	}

	/**
	 * @param typename the typename to set
	 */
	public void setTypename(String typename) {
		this.typename = typename;
	}
	
}
