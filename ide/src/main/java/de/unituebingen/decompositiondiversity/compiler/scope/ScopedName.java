/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler.scope;

/**
 * @author Fayez Abu Alia
 *
 */
public class ScopedName {

	private MODIFIER modifier;
	private QualifiedName qName;
	
	public ScopedName(MODIFIER modifier, QualifiedName qName) {
		this.modifier = modifier;
		this.qName = qName;
	}

	public MODIFIER getModifier() {
		return modifier;
	}

	public void setModifier(MODIFIER modifier) {
		this.modifier = modifier;
	}

	public QualifiedName getqName() {
		return qName;
	}
	
	public void setqName(QualifiedName qName) {
		this.qName = qName;
	}
	
	@Override
	public String toString() {
		
		return modifier.name()+ " " + qName.toString();
	}
}
