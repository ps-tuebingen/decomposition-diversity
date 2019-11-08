package de.unituebingen.decompositiondiversity.compiler.parser.error;

import de.unituebingen.decompositiondiversity.compiler.parser.exception.DecompositionDiversityException;

public class DuplicateNameException extends DecompositionDiversityException {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * @param message
	 */
	public DuplicateNameException(String message) {
		super(message);
	}
	
	
}
