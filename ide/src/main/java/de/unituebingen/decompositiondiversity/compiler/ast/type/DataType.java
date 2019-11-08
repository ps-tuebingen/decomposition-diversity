/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler.ast.type;

import java.util.List;

import org.antlr.v4.runtime.Token;

import de.unituebingen.decompositiondiversity.compiler.ast.ConstructorOrDestructor;
import de.unituebingen.decompositiondiversity.compiler.typechecker.SkeletonVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class DataType extends Type {

	public DataType(Token start, String typeName, List<ConstructorOrDestructor> body) {
		super(start, typeName, body);
	}
	
	@Override
	public void accept(SkeletonVisitor visitor) {
		visitor.visit(this);
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("Datatype: "+typeName +" \n\t");
		for(ConstructorOrDestructor cd : body) {
			sb.append(cd.toString());
		}
		return sb.toString();
	}
}
