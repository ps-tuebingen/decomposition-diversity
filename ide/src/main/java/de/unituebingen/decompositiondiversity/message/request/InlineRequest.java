/**
 * 
 */
package de.unituebingen.decompositiondiversity.message.request;

/**
 * @author Fayez Abu Alia
 *
 */
public class InlineRequest implements Request {
	private String source;
	private String name;

	public String getSource() {
		return source;
	}

	public void setSource(String source) {
		this.source = source;
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

}
