package de.unituebingen.decompositiondiversity.compiler.ast.expression;

import java.util.List;

import org.antlr.v4.runtime.Token;
import org.json.JSONObject;

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
public class Match extends MatchOrComatch {
    @Getter @Setter
    private Expression expr;
    @Getter @Setter
    private String returnType;

    public Match(Token start, Token stop, String type, QualifiedName qName,Expression expr, 
                 List<ExprDecl> expressionDeclList, List<CaseOrCocase> body, 
                 String returnType) {
        super(start, stop, returnType, qName, expressionDeclList, body);
        this.expr = expr;
        this.returnType = returnType;
    }

    @Override
    public Boolean accept(ExpressionVisitor<Boolean> visitor) {
        return visitor.visit(this);
    }

    @Override
    public JSONObject acceptJSONGen(ExpressionVisitor<JSONObject> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("Match\n\t\t");
        sb.append("QualifiedName = "+qName.toString() + "\n\t\texpression = "+ expr.toString());
        sb.append("\t\texprDeclList = ");
        for(ExprDecl e : expressionDeclList) {
            sb.append(e.toString()+" ");
        }
        sb.append(" \n\t\t returnType = "+returnType+"\n\t\t\tBody:\n\t\t\t\t");
        for(CaseOrCocase cc : body) {
            sb.append(cc.toString() + "\n\t\t\t\t");
        }
        sb.append("\n");
        return sb.toString();
    }

    @Override
    public String getInfo() {
        return "match " + qName.getName();
    }

    @Override
    public Expression acceptFinder(ExpressionVisitor<Expression> visitor) {
        return visitor.visit(this);
    }
}
