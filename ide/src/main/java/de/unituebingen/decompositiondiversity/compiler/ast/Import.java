package de.unituebingen.decompositiondiversity.compiler.ast;

/**
 * @author Fayez Abu Alia
 *
 */
public class Import {
    public enum TRANSFORMATION{
        Refunc,
        Defunc
    }

    private String name;
    private TRANSFORMATION trans;

    /**
     * @param name
     * @param trans
     */
    public Import(String name, TRANSFORMATION trans) {
        super();
        this.name = name;
        this.trans = trans;
    }

    @Override
    public String toString() {
        String tt = trans==TRANSFORMATION.Refunc?"R":"D";
        return "import "+ name + ":" + tt;
    }
}
