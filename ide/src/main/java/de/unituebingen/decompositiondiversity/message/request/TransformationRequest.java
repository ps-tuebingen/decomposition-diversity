package de.unituebingen.decompositiondiversity.message.request;

/**
 * Transformation request consists of type of
 * transformation and type name.
 * 
 * @author Fayez Abu Alia
 *
 */
public class TransformationRequest implements Request {
	/**
	 * The type of transformation: "refunc" or "defunc"
	 */
	private String type;
	/**
	 * The type name on which the transformation should be performed
	 */
	private String typename;

	public String getType() {
		return type;
	}

	public void setType(String type) {
		this.type = type;
	}

	public String getTypename() {
		return typename;
	}

	public void setTypename(String typename) {
		this.typename = typename;
	}
}
