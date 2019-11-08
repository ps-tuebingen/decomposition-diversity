package de.unituebingen.decompositiondiversity.compiler.ast.function;

import java.util.ArrayList;

import org.antlr.v4.runtime.Token;

import lombok.Getter;
import lombok.Setter;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Expression;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;
import de.unituebingen.decompositiondiversity.compiler.typechecker.SkeletonVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class OneExprFunction extends Function {
    @Getter @Setter
    private String name;
    @Getter @Setter
    private Expression body;

    public OneExprFunction(Token start, Token stop, String name, ArrayList<Variable> arguments,
                           String returnType, Expression body,ArrayList<Variable> localVars) {
        super(start, stop, arguments, returnType, localVars);
        this.name = name;
        this.body = body;
    }

    public void accept(SkeletonVisitor visitor) {
        visitor.visit(this);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("function: "+name +" - type: "+returnType+" - Arguments: ");
        for(Variable v : arguments) {
            sb.append(v.toString());
            sb.append(" , ");
        }

        sb.append("\n");

        sb.append(body.toString());
        sb.append("\n");
        return sb.toString();
    }
}
