package de.unituebingen.decompositiondiversity.compiler.ast.expression;

import java.util.List;

import org.antlr.v4.runtime.Token;

import lombok.Getter;
import lombok.Setter;
import de.unituebingen.decompositiondiversity.compiler.scope.ScopedName;

/**
 * @author Fayez Abu Alia
 *
 */
public abstract class ConstOrDestrCall extends Expression {
    protected ScopedName sName;
    @Getter @Setter
    protected List<Expression> expressionList;

    public ConstOrDestrCall(Token start, Token stop, String type, ScopedName sName,
                            List<Expression> expressionList) {
        super(start, stop, type);
        this.sName = sName;
        this.expressionList = expressionList;
    }
    public ScopedName getsName() {
        return sName;
    }

    public void setsName(ScopedName sName) {
        this.sName = sName;
    }
}
