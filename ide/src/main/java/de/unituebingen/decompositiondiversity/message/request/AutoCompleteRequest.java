/**
 * 
 */
package de.unituebingen.decompositiondiversity.message.request;

import java.util.ArrayList;

/**
 * Auto complete request.
 *  
 * @author Fayez Abu Alia
 */
public class AutoCompleteRequest implements Request {
	/**
	 * "data" or "codata"
	 */
	private String type;
	/**
	 * The Variables of the function or local expression. 
	 */
	private ArrayList<String> vars;
	/**
	 * The type name.
	 */
	private String typename;
	/**
	 * The start position.
	 */
	private int start;
	/**
	 * The current position.
	 */
	private int col;

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

	public int getStart() {
		return start;
	}

	public ArrayList<String> getVars() {
		return vars;
	}

	public void setVars(ArrayList<String> vars) {
		this.vars = vars;
	}

	public void setStart(int start) {
		this.start = start;
	}

	public int getCol() {
		return col;
	}

	public void setCol(int col) {
		this.col = col;
	}

}
