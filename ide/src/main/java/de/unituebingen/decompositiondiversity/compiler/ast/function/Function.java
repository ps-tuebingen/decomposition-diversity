package de.unituebingen.decompositiondiversity.compiler.ast.function;

import java.util.ArrayList;
import java.util.Map;

import org.antlr.v4.runtime.Token;

import lombok.Getter;
import lombok.Setter;
import de.unituebingen.decompositiondiversity.compiler.ast.ASTNode;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;
import de.unituebingen.decompositiondiversity.compiler.typechecker.SkeletonVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public abstract class Function extends ASTNode {
    protected String name;
    @Getter @Setter
    protected ArrayList<Variable> arguments;
    @Getter @Setter
    protected String returnType;
    @Getter
    protected final ArrayList<Variable> localVars;

    public Function(Token start, Token stop,ArrayList<Variable> arguments, String returnType,
                    ArrayList<Variable> localVars) {
        super(start, stop);
        this.arguments = arguments;
        this.returnType = returnType;
        this.localVars = localVars;
    }

    public abstract void accept(SkeletonVisitor visitor);
}
