package de.unituebingen.decompositiondiversity.compiler.ast;

import java.util.List;

import lombok.Getter;
import lombok.Setter;
import de.unituebingen.decompositiondiversity.compiler.ast.function.Function;
import de.unituebingen.decompositiondiversity.compiler.ast.type.Type;
import de.unituebingen.decompositiondiversity.compiler.parser.NullToken;
import de.unituebingen.decompositiondiversity.compiler.typechecker.SkeletonVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class Program extends ASTNode {
    @Getter @Setter
    private List<Import> imports;
    @Getter @Setter
    private List<Type> typeDeclerations;
    @Getter @Setter
    private List<Function> functionDeclerations;

    /**
     * @param typeDeclerations
     * @param functionDeclerations
     */
    public Program(List<Type> typeDeclerations, List<Function> functionDeclerations, List<Import> imports) {
        super(new NullToken(), new NullToken());
        this.typeDeclerations = typeDeclerations;
        this.functionDeclerations = functionDeclerations;
        this.imports = imports;
    }

    public void accept(SkeletonVisitor visitor) {
        visitor.visit(this);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        for(Type t: typeDeclerations) {
            sb = sb.append(t.toString());
            sb.append("\n");
        }
        sb.append("\n");
        for(Function f: functionDeclerations) {
            sb = sb.append(f.toString());
            sb.append("\n");
        }
        return sb.toString();
    }
}
