/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler.ast.type;

import java.util.ArrayList;
import java.util.List;

import org.antlr.v4.runtime.Token;

import de.unituebingen.decompositiondiversity.compiler.ast.ConstructorOrDestructor;
import de.unituebingen.decompositiondiversity.compiler.ast.function.Function;
import de.unituebingen.decompositiondiversity.compiler.typechecker.SkeletonVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public abstract class Type {
	protected Token start;
	protected String typeName;
	protected List<ConstructorOrDestructor> body;
	protected List<Function> allFunctions = new ArrayList<>();
	
	public Type(Token start, String typeName, List<ConstructorOrDestructor> body) {
		this.start = start;
		this.typeName = typeName;
		this.body = body;
	}
	
	public String getTypeName() {
		return typeName;
	}
	
	public void setTypeName(String typeName) {
		this.typeName = typeName;
	}
	
	public List<ConstructorOrDestructor> getBody() {
		return body;
	}
	
	public void setBody(List<ConstructorOrDestructor> body) {
		this.body = body;
	}
	
	public List<Function> getAllFunctions() {
		return allFunctions;
	}
	
	public void setAllFunctions(List<Function> allFunctions) {
		this.allFunctions = allFunctions;
	}
	public Token getStart() {
		return start;
	}
	
	public abstract void accept(SkeletonVisitor visitor);
}
