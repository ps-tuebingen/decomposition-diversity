/**
 * 
 */
package de.unituebingen.decompositiondiversity.helper;

import java.util.ArrayList;
import java.util.List;

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

/**
 * @author Fayez Abu Alia
 *
 */
public class VariableFinder implements ExpressionVisitor<Boolean> {
	private final List<Variable> vars = new ArrayList<>();

	private final String type;

	/**
	 * @param type
	 */
	public VariableFinder(String type) {
		super();
		this.type = type;
	}

	public List<Variable> getVars() {
		return vars;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.Variable)
	 */
	@Override
	public Boolean visit(Variable variable) {
		if (variable.getType().equals(type)) {
			vars.add(variable);
			return true;
		}
		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.ConstructorCall)
	 */
	@Override
	public Boolean visit(ConstructorCall constCall) {
		boolean found = false;

		for (Expression exp : constCall.getExpressionList()) {
			found |= exp.accept(this);
		}

		return found;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.DestructorCall)
	 */
	@Override
	public Boolean visit(DestructorCall destrCall) {
		boolean found = destrCall.getReceiver().accept(this);

		for (Expression exp : destrCall.getExpressionList()) {
			found |= exp.accept(this);
		}

		return found;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.FunctionCall)
	 */
	@Override
	public Boolean visit(FunctionCall funCall) {
		boolean found = false;
		for (Expression exp : funCall.getExpressions()) {
			found |= exp.accept(this);
		}

		return found;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.ComatchFunCall)
	 */
	@Override
	public Boolean visit(ComatchFunCall mFunCall) {
		boolean found = false;

		for (Expression exp : mFunCall.getExpressionList()) {
			found |= exp.accept(this);
		}

		return found;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.MatchFunCall)
	 */
	@Override
	public Boolean visit(MatchFunCall cmFunCall) {
		boolean found = cmFunCall.getReceiver().accept(this);

		for (Expression exp : cmFunCall.getExpressionList()) {
			found |= exp.accept(this);
		}

		return found;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.Match)
	 */
	@Override
	public Boolean visit(Match match) {
		boolean found = match.getExpr().accept(this);

		for (ExprDecl ed : match.getExpressionDeclList()) {
			found |= ed.accept(this);
		}

		for (CaseOrCocase cc : match.getBody()) {
			found |= cc.accept(this);
		}

		return found;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.Comatch)
	 */
	@Override
	public Boolean visit(Comatch comatch) {
		boolean found = false;

		for (ExprDecl ed : comatch.getExpressionDeclList()) {
			found |= ed.accept(this);
		}

		for (CaseOrCocase cc : comatch.getBody()) {
			found |= cc.accept(this);
		}

		return found;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.Let)
	 */
	@Override
	public Boolean visit(Let let) {
		return let.getLeft().accept(this) || let.getRight().accept(this);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase)
	 */
	@Override
	public Boolean visit(CaseOrCocase caseOrCo) {
		boolean found = false;
		for(Variable v : caseOrCo.getParams()) {
			found |= v.accept(this);
		}
		
		found |= caseOrCo.getExpr().accept(this);
		return found;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.ExprDecl)
	 */
	@Override
	public Boolean visit(ExprDecl exprD) {
		return exprD.getRight().accept(this);
	}

}
