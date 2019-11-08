package de.unituebingen.decompositiondiversity.compiler.ast;

import org.antlr.v4.runtime.Token;
import org.json.JSONObject;

import lombok.Getter;
import lombok.Setter;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Expression;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;

/**
 *
 * @author Fayez Abu Alia
 *
 */
public class ExprDecl extends ASTNode {
    @Getter @Setter
    private Variable left;

    @Getter @Setter
    private Expression right;

    @Getter @Setter
    private String type;

    /**
     * @param left
     * @param right
     * @param type
     */
    public ExprDecl(Token start, Token stop, Variable left, Expression right, String type) {
        super(start, stop);
        this.left = left;
        this.right = right;
        this.type = type;
    }

    public Boolean accept(ExpressionVisitor<Boolean> visitor) {
        return visitor.visit(this);
    }

    public JSONObject acceptJSONGen(ExpressionVisitor<JSONObject> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("ExprDecl: left: "+left.toString() +" right: "+right.toString()+" type "+ type);
        return sb.toString();
    }
}
