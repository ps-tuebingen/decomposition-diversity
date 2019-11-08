/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler.typechecker;

import de.unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase;
import de.unituebingen.decompositiondiversity.compiler.ast.ExprDecl;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Comatch;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.ComatchFunCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.ConstructorCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.DestructorCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.FunctionCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Let;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Match;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.MatchFunCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;

/**
 * @author Fayez Abu Alia
 *
 */
public interface ExpressionVisitor<T> {
	
	public T visit(Variable variable);

	public T visit(ConstructorCall constCall);

	public T visit(DestructorCall destrCall);

	public T visit(FunctionCall funCall);

	public T visit(ComatchFunCall mFunCall);

	public T visit(MatchFunCall cmFunCall);

	public T visit(Match match);

	public T visit(Comatch comatch);

	public T visit(Let let);

	public T visit(CaseOrCocase caseOrCo);

	public T visit(ExprDecl exprD);
}
