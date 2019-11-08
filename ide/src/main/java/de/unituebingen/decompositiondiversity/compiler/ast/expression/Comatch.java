package de.unituebingen.decompositiondiversity.compiler.ast.expression;

import java.util.List;

import org.antlr.v4.runtime.Token;
import org.json.JSONObject;

import de.unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase;
import de.unituebingen.decompositiondiversity.compiler.ast.ExprDecl;
import de.unituebingen.decompositiondiversity.compiler.scope.QualifiedName;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class Comatch extends MatchOrComatch {

    public Comatch(Token start, Token stop,String type, QualifiedName qName, List<ExprDecl> expressionDeclList,
                   List<CaseOrCocase> body) {
        super(start, stop, type, qName, expressionDeclList, body);
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
        StringBuilder sb = new StringBuilder("comatch");
        sb.append(qName.toString() + " [ ");
        int s = expressionDeclList.size();
        int i = 0;
        for(ExprDecl e : expressionDeclList) {
            ++i;
            sb.append(e.toString());
            if(i != s)
                sb.append(" , ");
        }
        sb.append("] \n");
        for(CaseOrCocase cc : body) {
            sb.append(cc.toString() + "\n");
        }
        return sb.toString();
    }

    @Override
    public String getInfo() {
        return "comatch " + qName.getName();
    }

    @Override
    public Expression acceptFinder(ExpressionVisitor<Expression> visitor) {
        return visitor.visit(this);
    }
}
