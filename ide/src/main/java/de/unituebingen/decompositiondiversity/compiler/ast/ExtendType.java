package de.unituebingen.decompositiondiversity.compiler.ast;

import lombok.Getter;
import lombok.Setter;

/**
 * @author Fayez Abu Alia
 *
 */
public class ExtendType extends Extend {
    @Getter @Setter
    private String typeName;
    @Getter @Setter
    private ConstructorOrDestructor element;

    /**
     * @param cc
     */
    public ExtendType(CaseOrCocase cc, String typeName, ConstructorOrDestructor element) {
        super(cc);
        this.typeName = typeName;
        this.element = element;
    }
}
