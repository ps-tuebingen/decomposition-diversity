package de.unituebingen.decompositiondiversity.compiler.ast;

import java.util.List;

import org.antlr.v4.runtime.Token;
import org.json.JSONObject;

import lombok.Getter;
import lombok.Setter;

import de.unituebingen.decompositiondiversity.compiler.ast.expression.Expression;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;
import de.unituebingen.decompositiondiversity.compiler.scope.ScopedName;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class CaseOrCocase extends ASTNode {
    @Getter @Setter
    private ScopedName name;

    @Getter @Setter
    private List<Variable> params;

    @Getter @Setter
    private Expression expr;

    public CaseOrCocase(Token start, Token stop, ScopedName name, List<Variable> params, Expression expr) {
        super(start, stop);
        this.name = name;
        this.params = params;
        this.expr = expr;
    }

    public JSONObject acceptJSONGen(ExpressionVisitor<JSONObject> visitor) {
        return visitor.visit(this);
    }

    public Boolean accept(ExpressionVisitor<Boolean> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("CaseOrCocase:  " + name + " - arguments: ");
        for (Variable v : params) {
            sb.append(v.getName().toString() + " type: " + v.getType() + " ,");
        }
        sb.append(" - expr: " + expr.toString());
        sb.append(" \n");
        return sb.toString();
    }
}
