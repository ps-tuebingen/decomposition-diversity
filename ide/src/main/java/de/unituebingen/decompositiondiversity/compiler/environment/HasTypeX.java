/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler.environment;

import de.unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase;
import de.unituebingen.decompositiondiversity.compiler.ast.ExprDecl;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Comatch;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.ComatchFunCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.ConstructorCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.DestructorCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Expression;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.FunctionCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Let;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Match;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.MatchFunCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;
import de.unituebingen.decompositiondiversity.helper.Constants;

/**
 * @author Fayez Abu Alia
 *
 */
public class HasTypeX implements ExpressionVisitor<Boolean> {

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.
	 * decompositiondiversity.ast.expression.Variable)
	 */
	@Override
	public Boolean visit(Variable variable) {

		return variable.getType().contains("$X$");
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.
	 * decompositiondiversity.ast.expression.ConstructorCall)
	 */
	@Override
	public Boolean visit(ConstructorCall constCall) {
		boolean hasX = constCall.getsName().getqName().getTypeName().contains("$X$") || constCall.getType().contains("$X$");
		if (hasX)
			return hasX;
		for (Expression e : constCall.getExpressionList()) {
			boolean exHasX = e.accept(this);
			if (exHasX)
				return true;
		}
		return hasX;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.
	 * decompositiondiversity.ast.expression.DestructorCall)
	 */
	@Override
	public Boolean visit(DestructorCall destrCall) {
		boolean hasX = destrCall.getsName().getqName().getTypeName().contains("$X$")
				|| destrCall.getType().contains("$X$") || destrCall.getReceiver().accept(this);

		if (hasX)
			return hasX;

		for (Expression e : destrCall.getExpressionList()) {
			boolean exHasX = e.accept(this);
			if (exHasX)
				return true;
		}
		return hasX;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.
	 * decompositiondiversity.ast.expression.FunctionCall)
	 */
	@Override
	public Boolean visit(FunctionCall funCall) {
		boolean hasX = funCall.getType().contains("$X$");
		if (hasX)
			return hasX;

		for (Expression e : funCall.getExpressions()) {
			boolean exHasX = e.accept(this);
			if (exHasX)
				return true;
		}
		return hasX;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.
	 * decompositiondiversity.ast.expression.ComatchFunCall)
	 */
	@Override
	public Boolean visit(ComatchFunCall mFunCall) {
		boolean hasX = mFunCall.getType().contains("$X$");
		if (hasX)
			return hasX;

		for (Expression e : mFunCall.getExpressionList()) {
			boolean exHasX = e.accept(this);
			if (exHasX)
				return true;
		}
		return hasX;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.
	 * decompositiondiversity.ast.expression.MatchFunCall)
	 */
	@Override
	public Boolean visit(MatchFunCall cmFunCall) {
		boolean hasX = cmFunCall.getType().contains("$X$") || cmFunCall.getReceiver().accept(this);
		if (hasX)
			return hasX;

		for (Expression e : cmFunCall.getExpressionList()) {
			boolean exHasX = e.accept(this);
			if (exHasX)
				return true;
		}
		return hasX;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.
	 * decompositiondiversity.ast.expression.Match)
	 */
	@Override
	public Boolean visit(Match match) {
		boolean hasX = match.getType().contains("$X$") || match.getExpr().accept(this)
				|| match.getReturnType().contains("$X$");
		if (hasX)
			return hasX;

		for (ExprDecl e : match.getExpressionDeclList()) {
			boolean exHasX = e.accept(this);
			if (exHasX)
				return true;
		}

		for (CaseOrCocase cc : match.getBody()) {
			if (cc.getExpr().accept(this))
				return true;
		}
		return hasX;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.
	 * decompositiondiversity.ast.expression.Comatch)
	 */
	@Override
	public Boolean visit(Comatch comatch) {
		boolean hasX = comatch.getType().contains("$X$");
		if (hasX)
			return hasX;

		for (ExprDecl e : comatch.getExpressionDeclList()) {
			boolean exHasX = e.accept(this);
			if (exHasX)
				return true;
		}

		for (CaseOrCocase cc : comatch.getBody()) {
			if (cc.getExpr().accept(this))
				return true;
		}
		return hasX;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.
	 * decompositiondiversity.ast.expression.Let)
	 */
	@Override
	public Boolean visit(Let let) {
		return let.getType().contains("$X$") || let.getRight().accept(this) || let.getLeft().accept(this);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.
	 * decompositiondiversity.ast.CaseOrCocase)
	 */
	@Override
	public Boolean visit(CaseOrCocase caseOrCo) {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.
	 * decompositiondiversity.ast.ExprDecl)
	 */
	@Override
	public Boolean visit(ExprDecl exprD) {
		return exprD.getLeft().accept(this) || exprD.getRight().accept(this) || exprD.getType().contains("$X$");
	}

}
