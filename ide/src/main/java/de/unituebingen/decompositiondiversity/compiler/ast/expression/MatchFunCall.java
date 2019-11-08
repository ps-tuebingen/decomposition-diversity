package de.unituebingen.decompositiondiversity.compiler.ast.expression;

import java.util.List;

import org.antlr.v4.runtime.Token;
import org.json.JSONObject;

import lombok.Getter;
import lombok.Setter;
import de.unituebingen.decompositiondiversity.compiler.scope.MODIFIER;
import de.unituebingen.decompositiondiversity.compiler.scope.QualifiedName;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class MatchFunCall extends MatchOrComatchFunCall {
    @Getter @Setter
    private Expression receiver;

    /**
     * @param type
     * @param token
     * @param qName
     * @param expressionList
     */
    public MatchFunCall(Token start, Token stop, String type, QualifiedName qName, 
			List<Expression> expressionList, Expression receiver) {
        super(start, stop, type, qName, expressionList);
        this.receiver = receiver;
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
        StringBuilder sb = new StringBuilder("MatchFunCall: ");
        sb.append(MODIFIER.GLOBAL+" " + qName.toString() + " -  receiver: " + receiver.toString());
        sb.append(" - expressionList = [");
        for(Expression e : expressionList) {
            sb.append(e.toString()+" ");
            sb.append(" , ");
        }
        sb.append("]\n");
        return sb.toString();
    }

    @Override
    public String getInfo() {
        return "match function call " + qName.getName();
    }

    @Override
    public Expression acceptFinder(ExpressionVisitor<Expression> visitor) {
        return visitor.visit(this);
    }
}
