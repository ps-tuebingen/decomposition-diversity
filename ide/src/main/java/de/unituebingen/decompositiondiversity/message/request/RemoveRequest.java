/**
 * 
 */
package de.unituebingen.decompositiondiversity.message.request;

/**
 * Remove cons-/destructor request
 * 
 * @author Fayez Abu Alia
 *
 */
public class RemoveRequest implements Request {
	
	/**
	 * The name of the cons-/destructor that will be
	 * remove from the program.
	 */
	private String name;
	/**
	 * "constructor" or "destructor"
	 */
	private String type;
	
	private String typename;
	
	public String getName() {
		return name;
	}
	public void setName(String name) {
		this.name = name;
	}
	public String getType() {
		return type;
	}
	public void setType(String type) {
		this.type = type;
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
