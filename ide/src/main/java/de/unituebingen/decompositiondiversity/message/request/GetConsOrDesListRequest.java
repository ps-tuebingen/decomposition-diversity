package de.unituebingen.decompositiondiversity.message.request;

public class GetConsOrDesListRequest implements Request {
//	private String type;
	private String typename;
//	/**
//	 * @return the type
//	 */
//	public String getType() {
//		return type;
//	}
//	/**
//	 * @param type the type to set
//	 */
//	public void setType(String type) {
//		this.type = type;
//	}
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
