package de.unituebingen.decompositiondiversity.compiler.ast.expression;

import java.util.List;

import org.antlr.v4.runtime.Token;

import lombok.Getter;
import lombok.Setter;
import de.unituebingen.decompositiondiversity.compiler.scope.QualifiedName;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public abstract class MatchOrComatchFunCall extends Expression{
    protected QualifiedName qName;
    @Getter @Setter
    protected List<Expression> expressionList;

    public MatchOrComatchFunCall(Token start, Token stop, String type, QualifiedName qName,
                                 List<Expression> expressionList) {
        super(start, stop, type);
        this.qName = qName;
        this.expressionList = expressionList;
    }

    public QualifiedName getqName() {
        return qName;
    }

    public void setsName(QualifiedName qName) {
        this.qName = qName;
    }

    public abstract Expression acceptFinder(ExpressionVisitor<Expression> visitor);
}
