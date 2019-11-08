/**
 * 
 */
package de.unituebingen.decompositiondiversity.helper;

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
public class RecursiveCallFinder implements ExpressionVisitor<Boolean> {
	private String name;
	
	/**
	 * @param name
	 */
	public RecursiveCallFinder(String name) {
		super();
		this.name = name;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.Variable)
	 */
	@Override
	public Boolean visit(Variable variable) {
		return false;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.ConstructorCall)
	 */
	@Override
	public Boolean visit(ConstructorCall constCall) {
		boolean found = false;
		for(Expression ex:constCall.getExpressionList()) {
			found |= ex.accept(this);
		}
		
		return found;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.DestructorCall)
	 */
	@Override
	public Boolean visit(DestructorCall destrCall) {
		boolean found = destrCall.getReceiver().accept(this);
		for(Expression ex:destrCall.getExpressionList()) {
			found |= ex.accept(this);
		}
		
		return found;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.FunctionCall)
	 */
	@Override
	public Boolean visit(FunctionCall funCall) {
		boolean found = false;
		for(Expression ex:funCall.getExpressions()) {
			found |= ex.accept(this);
		}
		
		return found;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.ComatchFunCall)
	 */
	@Override
	public Boolean visit(ComatchFunCall mFunCall) {
		if(mFunCall.getqName().getName().equals(name))
			return true;
		
		boolean found = false;
		for(Expression ex:mFunCall.getExpressionList()) {
			found |= ex.accept(this);
		}
		
		return found;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.MatchFunCall)
	 */
	@Override
	public Boolean visit(MatchFunCall cmFunCall) {
		if(cmFunCall.getqName().getName().equals(name))
			return true;
		
		boolean found = cmFunCall.getReceiver().accept(this);
		for(Expression ex:cmFunCall.getExpressionList()) {
			found |= ex.accept(this);
		}
		
		return found;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.Match)
	 */
	@Override
	public Boolean visit(Match match) {
		boolean found = match.getExpr().accept(this);
		
		for(ExprDecl exd : match.getExpressionDeclList()) {
			found |= exd.getRight().accept(this); 
		}
		
		for(CaseOrCocase cc : match.getBody()) {
			found |= cc.getExpr().accept(this);
		}
		
		return found;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.Comatch)
	 */
	@Override
	public Boolean visit(Comatch comatch) {
		boolean found = false;
		
		for(ExprDecl exd : comatch.getExpressionDeclList()) {
			found |= exd.getRight().accept(this); 
		}
		
		for(CaseOrCocase cc : comatch.getBody()) {
			found |= cc.getExpr().accept(this);
		}
		
		return found;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.Let)
	 */
	@Override
	public Boolean visit(Let let) {
		return let.getLeft().getRight().accept(this) || let.getRight().accept(this);
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.CaseOrCocase)
	 */
	@Override
	public Boolean visit(CaseOrCocase caseOrCo) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.ExprDecl)
	 */
	@Override
	public Boolean visit(ExprDecl exprD) {
		// TODO Auto-generated method stub
		return null;
	}

}
