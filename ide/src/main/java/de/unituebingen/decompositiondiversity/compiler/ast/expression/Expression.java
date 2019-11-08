package de.unituebingen.decompositiondiversity.compiler.ast.expression;

import org.antlr.v4.runtime.Token;
import org.json.JSONObject;

import lombok.Getter;
import lombok.Setter;
import de.unituebingen.decompositiondiversity.compiler.ast.ASTNode;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public abstract class Expression extends ASTNode {
    @Getter @Setter
    protected String type;

    public Expression(Token start, Token stop, String type) {
        super(start, stop);
        this.type = type;
    }

    public abstract Boolean accept(ExpressionVisitor<Boolean> visitor);

    public abstract JSONObject acceptJSONGen(ExpressionVisitor<JSONObject> visitor);

    public abstract Expression acceptFinder(ExpressionVisitor<Expression> visitor);

    public abstract String getInfo();
}
