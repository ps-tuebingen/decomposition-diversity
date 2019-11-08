package de.unituebingen.decompositiondiversity.model;

import lombok.Getter;
import lombok.Setter;

/**
 *
 * @author Fayez Abu Alia
 *
 */
public class Editor {
    @Getter @Setter
    private String value;
    @Getter @Setter
    private String result;
    @Getter @Setter
    private Object program;
}
