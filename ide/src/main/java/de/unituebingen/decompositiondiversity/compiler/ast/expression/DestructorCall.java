package de.unituebingen.decompositiondiversity.compiler.ast.expression;

import java.util.List;

import org.antlr.v4.runtime.Token;
import org.json.JSONObject;

import lombok.Getter;
import lombok.Setter;
import de.unituebingen.decompositiondiversity.compiler.scope.ScopedName;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class DestructorCall extends ConstOrDestrCall {
    @Getter @Setter
    private Expression receiver;

    /**
     * @param type
     * @param token
     * @param sName
     * @param expressionList
     */
    public DestructorCall(Token start, Token stop, String type, ScopedName sName, 
                          List<Expression> expressionList,Expression receiver) {
        super(start, stop, type, sName, expressionList);
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
        StringBuilder sb = new StringBuilder("DesstructorCall: ");
        sb.append(sName.toString() +" - receiver: "+receiver +" - expressionList= [");
        for(Expression e : expressionList) {
            sb.append(e.toString()+" ");
            sb.append(" , ");
        }
        sb.append("]\n");

        return sb.toString();
    }

    @Override
    public String getInfo() {
        return "destructor call " + sName.getqName().getName();
    }


    @Override
    public Expression acceptFinder(ExpressionVisitor<Expression> visitor) {
        return visitor.visit(this);
    }
}
