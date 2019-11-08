package de.unituebingen.decompositiondiversity.compiler.ast.function;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.antlr.v4.runtime.Token;

import lombok.Getter;
import lombok.Setter;
import de.unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;
import de.unituebingen.decompositiondiversity.compiler.scope.QualifiedName;

/**
 * @author Fayez Abu Alia
 *
 */
public abstract class MatchOrCoMatchFunction extends Function {
    protected QualifiedName qName;
    @Getter @Setter
    protected List<CaseOrCocase> body;

    public MatchOrCoMatchFunction(Token start, Token stop, QualifiedName qName, ArrayList<Variable> arguments, 
                                  String returnType, List<CaseOrCocase> body, ArrayList<Variable> localVars) {
        super(start, stop, arguments, returnType,localVars);
        this.qName = qName;
        this.body = body;
    }

    public QualifiedName getqName() {
        return qName;
    }

    public void setqName(QualifiedName qName) {
        this.qName = qName;
    }
}
