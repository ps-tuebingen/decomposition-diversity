package de.unituebingen.decompositiondiversity.compiler.ast.expression;

import org.antlr.v4.runtime.Token;
import org.json.JSONObject;

import lombok.Getter;
import lombok.Setter;
import de.unituebingen.decompositiondiversity.compiler.ast.ExprDecl;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class Let extends Expression{
    @Getter @Setter
    private ExprDecl left;
    @Getter @Setter
    private Expression right;

    /**
     * @param type
     * @param token
     */
    public Let(Token start, Token stop, String type,ExprDecl left, Expression right) {
        super(start, stop,type);
        this.left = left;
        this.right = right;
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
        StringBuilder sb = new StringBuilder("Let: \n\t\t");
        sb.append("left:  " + left.toString() +"\n\t\tright: "+right.toString());
        return sb.toString();
    }

    @Override
    public String getInfo() {
        return "let ";
    }

    @Override
    public Expression acceptFinder(ExpressionVisitor<Expression> visitor) {
        return visitor.visit(this);
    }
}
