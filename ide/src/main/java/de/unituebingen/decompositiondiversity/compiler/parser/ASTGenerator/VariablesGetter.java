/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler.parser.ASTGenerator;

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
import de.unituebingen.decompositiondiversity.compiler.ast.function.Function;
import de.unituebingen.decompositiondiversity.compiler.parser.NullToken;
import de.unituebingen.decompositiondiversity.compiler.parser.exception.DecompositionDiversityException;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class VariablesGetter implements ExpressionVisitor<Boolean> {
	private List<Variable> varList;
	private List<ExprDecl> exprList;

	/**
	 * @param varList
	 */
	public VariablesGetter(List<Variable> varList, List<ExprDecl> exprList) {
		super();
		this.varList = varList;
		this.exprList = exprList;
	}

	private boolean inVarList(String text) {
		for (Variable v : varList) {
			if (v.getName().equals(text)) {
				return true;
			}
		}
		return false;
	}

	private boolean inExprList(String text) {
		for (ExprDecl ed : exprList) {
			if (ed.getLeft().getName().equals(text)) {
				return true;
			}
		}
		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.Variable)
	 */
	@Override
	public Boolean visit(Variable variable) {
		String name = variable.getName();
		if (inVarList(name) && !inExprList(name)) {
			ExprDecl ed = new ExprDecl(new NullToken(), new NullToken(), variable, getVar(name), variable.getType());
			exprList.add(ed);
			return true;
		}
		return false;
	}

	private Expression getVar(String name) {
		for (Variable v : varList) {
			if (v.getName().equals(name)) {
				return v;
			}
		}
		throw new DecompositionDiversityException("Variabe does not exist");
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.ConstructorCall)
	 */
	@Override
	public Boolean visit(ConstructorCall constCall) {
		boolean res = false;
		for (Expression ex : constCall.getExpressionList()) {
			res |= ex.accept(this);
		}
		return res;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.DestructorCall)
	 */
	@Override
	public Boolean visit(DestructorCall destrCall) {
		boolean res = destrCall.getReceiver().accept(this);

		for (Expression ex : destrCall.getExpressionList()) {
			res |= ex.accept(this);
		}
		return res;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.FunctionCall)
	 */
	@Override
	public Boolean visit(FunctionCall funCall) {
		boolean res = false;
		for (Expression ex : funCall.getExpressions()) {
			res |= ex.accept(this);
		}
		return res;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.ComatchFunCall)
	 */
	@Override
	public Boolean visit(ComatchFunCall mFunCall) {
		boolean res = false;
		for (Expression ex : mFunCall.getExpressionList()) {
			res |= ex.accept(this);
		}
		return res;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.MatchFunCall)
	 */
	@Override
	public Boolean visit(MatchFunCall cmFunCall) {
		boolean res = cmFunCall.getReceiver().accept(this);
		for (Expression ex : cmFunCall.getExpressionList()) {
			res |= ex.accept(this);
		}
		return res;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.Match)
	 */
	@Override
	public Boolean visit(Match match) {
		boolean res = match.getExpr().accept(this);
		for (ExprDecl ex : match.getExpressionDeclList()) {
			res |= ex.accept(this);
		}
		
		for (CaseOrCocase cc : match.getBody()) {
			res |= cc.accept(this);
		}
		
		return res;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.Comatch)
	 */
	@Override
	public Boolean visit(Comatch comatch) {
		boolean res = false;
		for (ExprDecl ex : comatch.getExpressionDeclList()) {
			res |= ex.accept(this);
		}
		
		for (CaseOrCocase cc : comatch.getBody()) {
			res |= cc.accept(this);
		}
		
		return res;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.Let)
	 */
	@Override
	public Boolean visit(Let let) {
		return let.getLeft().getRight().accept(this) || let.getRight().accept(this);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase)
	 */
	@Override
	public Boolean visit(CaseOrCocase caseOrCo) {
		
		return caseOrCo.getExpr().accept(this);
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
