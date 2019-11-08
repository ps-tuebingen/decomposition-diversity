package de.unituebingen.decompositiondiversity.compiler.ast.expression;

import java.util.List;

import org.antlr.v4.runtime.Token;
import org.json.JSONObject;

import de.unituebingen.decompositiondiversity.compiler.scope.MODIFIER;
import de.unituebingen.decompositiondiversity.compiler.scope.QualifiedName;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class ComatchFunCall extends MatchOrComatchFunCall {

    /**
     * @param type
     * @param token
     * @param qName
     * @param expressionList
     */
    public ComatchFunCall(Token start, Token stop, String type, QualifiedName qName, 
                          List<Expression> expressionList) {
        super(start, stop, type, qName, expressionList);
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
        StringBuilder sb = new StringBuilder("GenFunCall: ");
        sb.append(MODIFIER.GLOBAL +" "+ qName.toString());
        sb.append(" -  expressionList = [");
        for(Expression e : expressionList) {
            sb.append(e.toString()+" ");
            sb.append(", ");
        }
        sb.append("]\n");
        return sb.toString();
    }

    @Override
    public String getInfo() {
        return "comatch function call " + qName.getName();
    }

    @Override
    public Expression acceptFinder(ExpressionVisitor<Expression> visitor) {
        return visitor.visit(this);
    }
}
