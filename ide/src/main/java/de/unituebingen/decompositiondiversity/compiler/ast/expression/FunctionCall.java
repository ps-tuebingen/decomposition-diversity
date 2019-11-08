package de.unituebingen.decompositiondiversity.compiler.ast.expression;

import java.util.List;

import org.antlr.v4.runtime.Token;
import org.json.JSONObject;

import lombok.Getter;
import lombok.Setter;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class FunctionCall extends Expression {
    @Getter @Setter
    private String name;
    @Getter @Setter
    private List<Expression> expressions;

    /**
     * @param name
     * @param expressions
     */
    public FunctionCall(Token start, Token stop, String type,String name, 
			List<Expression> expressions) {
        super(start, stop, type);
        this.name = name;
        this.expressions = expressions;
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
        StringBuilder sb = new StringBuilder();
        sb.append("FunCall: " + name + " ExpressionList:[ ");
        for(Expression e : expressions) {
            sb.append(e.toString()+" ");
            sb.append(" , ");
        }
        sb.append("]\n");
        return sb.toString();
    }

    @Override
    public String getInfo() {
        return "function call " + name;
    }

    @Override
    public Expression acceptFinder(ExpressionVisitor<Expression> visitor) {
        return visitor.visit(this);
    }
}
