/**
 * 
 */
package de.unituebingen.decompositiondiversity.message.request;



/**
 * Add cons-/destructor request
 * 
 * @author Fayez Abu Alia
 *
 */
public class AddRequest implements Request {
	/**
	 * The source code.
	 */
	private String source;
	/**
	 * The body of co-/match function.
	 */
	private String body;
	/**
	 * "constructor" or "destructor"
	 */
	private String type;
	/**
	 * The name of the cons-/destructor that will be
	 * add to the program.
	 */
	private String name;

	public String getSource() {
		return source;
	}

	public void setSource(String source) {
		this.source = source;
	}
	
	public String getBody() {
		return body;
	}

	public void setBody(String body) {
		this.body = body;
	}

	public String getType() {
		return type;
	}

	public void setType(String type) {
		this.type = type;
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}
	
	
}
