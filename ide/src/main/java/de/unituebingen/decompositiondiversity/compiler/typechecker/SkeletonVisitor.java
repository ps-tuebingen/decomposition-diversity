/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler.typechecker;

import de.unituebingen.decompositiondiversity.compiler.ast.Constructor;
import de.unituebingen.decompositiondiversity.compiler.ast.Destructor;
import de.unituebingen.decompositiondiversity.compiler.ast.Program;
import de.unituebingen.decompositiondiversity.compiler.ast.function.CoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchFuction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.OneExprFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.type.CoDataType;
import de.unituebingen.decompositiondiversity.compiler.ast.type.DataType;

/**
 * @author Fayez Abu Alia
 *
 */
public interface SkeletonVisitor {
	public void visit(Program program);

	public void visit(DataType dataType);

	public void visit(CoDataType codataType);

	public void visit(Constructor constr);

	public void visit(Destructor destr);

	public void visit(OneExprFunction function);

	public void visit(MatchFuction function);

	public void visit(CoMatchFunction function);

}
