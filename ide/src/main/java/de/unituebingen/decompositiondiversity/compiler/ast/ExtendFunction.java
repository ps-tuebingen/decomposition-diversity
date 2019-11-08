package de.unituebingen.decompositiondiversity.compiler.ast;

import lombok.Getter;
import lombok.Setter;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchOrCoMatchFunction;

/**
 * @author Fayez Abu Alia
 *
 */
public class ExtendFunction extends Extend {
    @Getter @Setter
    private MatchOrCoMatchFunction function;

    /**
     * @param cc
     */
    public ExtendFunction(CaseOrCocase cc, MatchOrCoMatchFunction function) {
        super(cc);
        this.function = function;
    }
}
