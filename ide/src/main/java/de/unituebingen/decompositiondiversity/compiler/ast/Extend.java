package de.unituebingen.decompositiondiversity.compiler.ast;

import lombok.Getter;
import lombok.Setter;

/**
 * @author Fayez Abu Alia
 *
 */
public abstract class Extend {
    @Getter @Setter
    protected CaseOrCocase cc;

    /**
     * @param cc
     */
    public Extend(CaseOrCocase cc) {
        super();
        this.cc = cc;
    }
}
