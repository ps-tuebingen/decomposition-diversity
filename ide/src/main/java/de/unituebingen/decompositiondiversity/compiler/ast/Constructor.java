package de.unituebingen.decompositiondiversity.compiler.ast;

import java.util.ArrayList;

import org.antlr.v4.runtime.Token;

import de.unituebingen.decompositiondiversity.compiler.scope.ScopedName;
import de.unituebingen.decompositiondiversity.compiler.typechecker.SkeletonVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class Constructor extends ConstructorOrDestructor {

    public Constructor(Token start, Token stop, ScopedName sName, ArrayList<String> typeNames) {
        super(start,stop,sName,typeNames);
    }

    public void accept(SkeletonVisitor visitor) {
        visitor.visit(this);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("Constructor: " + sName.toString() + " [");
        for(String s : typeNames) {
            sb.append(s + " ");
        }
        sb.append("]\n\t");
        return sb.toString();
    }
}
