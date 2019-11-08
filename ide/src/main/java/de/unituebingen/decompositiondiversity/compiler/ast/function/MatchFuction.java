package de.unituebingen.decompositiondiversity.compiler.ast.function;

import java.util.ArrayList;
import java.util.List;

import org.antlr.v4.runtime.Token;

import lombok.Getter;
import lombok.Setter;
import de.unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;
import de.unituebingen.decompositiondiversity.compiler.scope.QualifiedName;
import de.unituebingen.decompositiondiversity.compiler.typechecker.SkeletonVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class MatchFuction extends MatchOrCoMatchFunction {
    @Getter @Setter
    private String receiverType;
    /**
     * @param qName
     * @param body
     */
    public MatchFuction(Token start, Token stop, String receiverType,QualifiedName qName, ArrayList<Variable> arguments,
			String returnType,List<CaseOrCocase> body,ArrayList<Variable> localVars) {
        super(start, stop, qName, arguments, returnType, body,localVars);
        this.receiverType = receiverType;
    }

    public void accept(SkeletonVisitor visitor) {
        visitor.visit(this);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("Match Function: "+qName.toString() +" - receiverType: "+receiverType+
                  " - return type : " + returnType +
                  " -  arguments: ");

        for(Variable v : arguments) {
            sb.append(v.toString());
            sb.append(" , ");
        }

        sb.append("\n");
        for(CaseOrCocase cc: body) {
            if(cc != null)
                sb.append(cc.toString());
        }

        return sb.toString();
    }
}
