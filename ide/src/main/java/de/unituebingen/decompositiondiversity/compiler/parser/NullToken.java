/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler.parser;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenSource;

/**
 * @author Fayez Abu Alia
 *
 */
public class NullToken implements Token {

	/* (non-Javadoc)
	 * @see org.antlr.v4.runtime.Token#getText()
	 */
	@Override
	public String getText() {
		return "";
	}

	/* (non-Javadoc)
	 * @see org.antlr.v4.runtime.Token#getType()
	 */
	@Override
	public int getType() {
		return 0;
	}

	/* (non-Javadoc)
	 * @see org.antlr.v4.runtime.Token#getLine()
	 */
	@Override
	public int getLine() {
		return 0;
	}

	/* (non-Javadoc)
	 * @see org.antlr.v4.runtime.Token#getCharPositionInLine()
	 */
	@Override
	public int getCharPositionInLine() {
		return 0;
	}

	/* (non-Javadoc)
	 * @see org.antlr.v4.runtime.Token#getChannel()
	 */
	@Override
	public int getChannel() {
		return 0;
	}

	/* (non-Javadoc)
	 * @see org.antlr.v4.runtime.Token#getTokenIndex()
	 */
	@Override
	public int getTokenIndex() {
		return 0;
	}

	/* (non-Javadoc)
	 * @see org.antlr.v4.runtime.Token#getStartIndex()
	 */
	@Override
	public int getStartIndex() {
		return 0;
	}

	/* (non-Javadoc)
	 * @see org.antlr.v4.runtime.Token#getStopIndex()
	 */
	@Override
	public int getStopIndex() {
		return 0;
	}

	/* (non-Javadoc)
	 * @see org.antlr.v4.runtime.Token#getTokenSource()
	 */
	@Override
	public TokenSource getTokenSource() {
		return null;
	}

	/* (non-Javadoc)
	 * @see org.antlr.v4.runtime.Token#getInputStream()
	 */
	@Override
	public CharStream getInputStream() {
		return null;
	}

}
