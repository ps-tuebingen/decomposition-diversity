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
public class Destructor extends ConstructorOrDestructor {

    @Getter @Setter
    private String returnType;

    public Destructor(Token start, Token stop, ScopedName sName,  ArrayList<String> typeNames, String returnType) {
        super(start,stop,sName,typeNames);
        this.returnType = returnType;
    }

    public void accept(SkeletonVisitor visitor) {
        visitor.visit(this);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("Destructor: " + sName.toString() + " (");
        for(String s : typeNames) {
            sb.append(s + " ");
        }
        sb.append(") : Returntype "+returnType +"\n\t");
        return sb.toString();
    }
}
