package de.unituebingen.decompositiondiversity.compiler.ast;

import lombok.Getter;
import lombok.Setter;
import org.antlr.v4.runtime.Token;

/**
 * @author Fayez Abu Alia
 *
 */
public abstract class ASTNode {
    @Getter @Setter
    protected Token start;

    @Getter @Setter
    protected Token stop;
    /**
     * @param start
     * @param stop
     */
    public ASTNode(Token start, Token stop) {
        this.start = start;
        this.stop = stop;
    }
}
