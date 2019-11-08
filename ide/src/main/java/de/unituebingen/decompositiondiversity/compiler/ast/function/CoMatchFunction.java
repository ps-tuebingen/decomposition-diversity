package de.unituebingen.decompositiondiversity.compiler.ast.function;

import java.util.ArrayList;
import java.util.List;

import org.antlr.v4.runtime.Token;

import de.unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;
import de.unituebingen.decompositiondiversity.compiler.scope.QualifiedName;
import de.unituebingen.decompositiondiversity.compiler.typechecker.SkeletonVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class CoMatchFunction extends MatchOrCoMatchFunction {
    /**
     * @param qName
     * @param body
     */
    public CoMatchFunction(Token start, Token stop, QualifiedName qName, ArrayList<Variable> arguments,
                           String returnType,List<CaseOrCocase> body, ArrayList<Variable> localVars) {
        super(start, stop, qName, arguments, returnType, body, localVars);
    }

    public void accept(SkeletonVisitor visitor) {
        visitor.visit(this);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("CoMatch Function: "+qName.toString() + " - type: " + this.returnType + 
                  " - arguments: ");

        for(Variable v : arguments) {
            sb.append(v.toString());
            sb.append(" , ");
        }

        sb.append("\n");
        for(CaseOrCocase cc: body) {
            sb.append(cc.toString());
        }

        return sb.toString();
    }
}
