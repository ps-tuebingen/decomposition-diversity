package de.unituebingen.decompositiondiversity.compiler.ast.expression;

import org.antlr.v4.runtime.Token;
import org.json.JSONObject;

import lombok.Getter;
import lombok.Setter;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class Variable extends Expression{
    @Getter @Setter
    private String name;

    public Variable(Token start, Token stop, String type, String name) {
        super(start, stop, type);
        this.name = name;
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
        return "Variable: " + name;
    }

    @Override
    public String getInfo() {
        return "variable " + name;
    }

    @Override
    public Expression acceptFinder(ExpressionVisitor<Expression> visitor) {
        return visitor.visit(this);
    }
}
