package de.unituebingen.decompositiondiversity.compiler.ast.expression;

import java.util.List;

import org.antlr.v4.runtime.Token;
import org.json.JSONObject;

import de.unituebingen.decompositiondiversity.compiler.scope.ScopedName;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class ConstructorCall extends ConstOrDestrCall {
    /**
     * @param type
     * @param token
     * @param sName
     * @param expressionList
     */
    public ConstructorCall(Token start, Token stop, String type, ScopedName sName, List<Expression> expressionList) {
        super(start, stop, type, sName, expressionList);
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
        StringBuilder sb = new StringBuilder("ConstructorCall: ");
        sb.append(sName.toString() + "expressionList= [");
        for(Expression e : expressionList) {
            sb.append(e.toString()+" ");
            sb.append(" , ");
        }
        sb.append("]\n");

        return sb.toString();
    }

    @Override
    public String getInfo() {
        return "constructor call " + sName.getqName().getName();
    }

    @Override
    public Expression acceptFinder(ExpressionVisitor<Expression> visitor) {
        return visitor.visit(this);
    }
}
