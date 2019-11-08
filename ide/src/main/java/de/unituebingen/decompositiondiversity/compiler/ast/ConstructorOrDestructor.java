package de.unituebingen.decompositiondiversity.compiler.ast;

import java.util.ArrayList;

import org.antlr.v4.runtime.Token;

import lombok.Getter;
import lombok.Setter;
import de.unituebingen.decompositiondiversity.compiler.scope.ScopedName;
import de.unituebingen.decompositiondiversity.compiler.typechecker.SkeletonVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public abstract class ConstructorOrDestructor extends ASTNode {
    protected ScopedName sName;
    // Type names of arguments of constructor/destructor

    @Getter @Setter
    protected ArrayList<String> typeNames;

    public ConstructorOrDestructor(Token start,Token stop, ScopedName sName, ArrayList<String> typeNames) {
        super(start, stop);
        this.sName = sName;
        this.typeNames = typeNames;
    }

    public ScopedName getsName() {
        return sName;
    }

    public void setsName(ScopedName sName) {
        this.sName = sName;
    }

    public abstract void accept(SkeletonVisitor visitor);
}
