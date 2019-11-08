package de.unituebingen.decompositiondiversity.compiler.ast.expression;

import java.util.List;

import org.antlr.v4.runtime.Token;

import lombok.Getter;
import lombok.Setter;
import de.unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase;
import de.unituebingen.decompositiondiversity.compiler.ast.ExprDecl;
import de.unituebingen.decompositiondiversity.compiler.scope.QualifiedName;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public abstract class MatchOrComatch extends Expression {
	protected QualifiedName qName;
    @Getter @Setter
    protected List<ExprDecl> expressionDeclList;
    @Getter @Setter
    protected List<CaseOrCocase> body;

    public MatchOrComatch(Token start, Token stop,String type, QualifiedName qName,
                          List<ExprDecl> expressionDeclList,List<CaseOrCocase> body) {
        super(start, stop, type);
        this.qName = qName;
        this.expressionDeclList = expressionDeclList;
        this.body = body;
    }

    public QualifiedName getqName() {
        return qName;
    }
    public void setqName(QualifiedName qName) {
        this.qName = qName;
    }
}
