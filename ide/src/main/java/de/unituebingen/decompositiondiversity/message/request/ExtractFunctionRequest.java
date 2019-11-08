/**
 * 
 */
package de.unituebingen.decompositiondiversity.message.request;

/**
 * @author Fayez Abu Alia
 *
 */
public class ExtractFunctionRequest implements Request {
	private String name;
	private String type;
	private String source;
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
	public String getSource() {
		return source;
	}
	public void setSource(String source) {
		this.source = source;
	}
	
	
}
