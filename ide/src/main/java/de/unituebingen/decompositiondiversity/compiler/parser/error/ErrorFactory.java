/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler.parser.error;

import java.util.ArrayList;

import de.unituebingen.decompositiondiversity.compiler.parser.error.Error.ErrorSeverity;

/**
 * @author Fayez Abu Alia
 *
 */
public class ErrorFactory {
	/**
	 * Generates warning: no constructors (or destructors) are defined
	 * 
	 * @param startLine
	 * @param endLine
	 * @param startCol
	 * @param endCol
	 * @return
	 */
	public static Error createWarning(int startLine, int endLine, int startCol, int endCol, String msg) {
		ErrorSeverity serv = ErrorSeverity.WARNING;
		
		Error warn = new Error(startLine, endLine, startCol, endCol, msg, serv, new ArrayList<>());
		return warn;
	}

	public static Error createError(int startLine, int endLine, int startCol, int endCol, String msg) {
		Error err = new Error(startLine, endLine, startCol, endCol, msg, ErrorSeverity.ERROR, new ArrayList<>());
		return err;
	}
}
