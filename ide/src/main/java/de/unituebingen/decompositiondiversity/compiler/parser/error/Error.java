/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler.parser.error;

import java.util.List;

import org.json.JSONObject;

/**
 * @author Fayez Abu Alia
 *
 */
public class Error {
	public enum ErrorSeverity{
		WARNING,
		ERROR
	}
	private int startLine;
	private int endLine;
	private int startCol;
	private int endCol;
	private String msg;
	private ErrorSeverity errSev;
	private final List<String> fixList;
	/**
	 * @param startLine
	 * @param endLine
	 * @param startCol
	 * @param endCol
	 * @param msg
	 * @param fixList
	 */
	public Error(int startLine, int endLine, int startCol, int endCol, String msg, 
			ErrorSeverity errSev, List<String> fixList) {
		super();
		this.startLine = startLine;
		this.endLine = endLine;
		this.startCol = startCol;
		this.endCol = endCol;
		this.msg = msg;
		this.errSev = errSev;
		this.fixList = fixList;
	}
	public int getStartLine() {
		return startLine;
	}
	public void setStartLine(int startLine) {
		this.startLine = startLine;
	}
	public int getEndLine() {
		return endLine;
	}
	public void setEndLine(int endLine) {
		this.endLine = endLine;
	}
	public int getStartCol() {
		return startCol;
	}
	public void setStartCol(int startCol) {
		this.startCol = startCol;
	}
	public int getEndCol() {
		return endCol;
	}
	public void setEndCol(int endCol) {
		this.endCol = endCol;
	}
	public String getMsg() {
		return msg;
	}
	public void setMsg(String msg) {
		this.msg = msg;
	}
	public ErrorSeverity getErrSev() {
		return errSev;
	}
	public void setErrSev(ErrorSeverity errSev) {
		this.errSev = errSev;
	}
	public List<String> getFixList() {
		return fixList;
	}
	
	@Override
	public String toString() {
		return "start line: " + startLine + " stop line: " + endLine + " start col" + startCol + 
				" end Col: " + endCol + " type: "+errSev.toString() + " msg: " + msg;
	}
	
	public JSONObject toJSON() {
    	JSONObject errJson = new JSONObject();
		errJson.put("line", startLine);
		errJson.put("stopLine", endLine);
		errJson.put("col", startCol);
		errJson.put("stopCol", endCol);
		
		errJson.put("message", msg);
		errJson.put("severity",errSev==ErrorSeverity.ERROR?"error":"warning");
		
		return errJson;
    }
}
