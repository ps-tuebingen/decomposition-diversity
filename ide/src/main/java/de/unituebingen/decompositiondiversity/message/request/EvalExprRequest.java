/**
 * 
 */
package de.unituebingen.decompositiondiversity.message.request;

/**
 * Evaluate expression request contains expression that
 * will be evaluated.
 * 
 * @author Fayez Abu Alia
 *
 */
public class EvalExprRequest implements Request {
	/**
	 * The expression to be evaluated.
	 */
	private String expr;

	public String getExpr() {
		return expr;
	}

	public void setExpr(String expr) {
		this.expr = expr;
	}
}
