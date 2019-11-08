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

/**
 * @author Fayez Abu Alia
 *
 */
public class TypeSetter implements ExpressionVisitor<Boolean> {
	
	private String typeX;
	private String typeToSet;
	
	/**
	 * @param typeX
	 * @param typeToSet
	 */
	public TypeSetter(String typeX, String typeToSet) {
		super();
		this.typeX = typeX;
		this.typeToSet = typeToSet;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.Variable)
	 */
	@Override
	public Boolean visit(Variable variable) {
		if(variable.getType().equals(typeX)) {
			variable.setType(typeToSet);
			return true;
		}
			
		return false;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.ConstructorCall)
	 */
	@Override
	public Boolean visit(ConstructorCall constCall) {
		boolean changed = false;
		if(constCall.getsName().getqName().getTypeName().equals(typeX)) {
			constCall.getsName().getqName().setTypeName(typeToSet);
			changed = true;
		}
		
		if(constCall.getType().equals(typeX)) {
			constCall.setType(typeToSet);
			changed = true;
		}
		
		for(Expression e : constCall.getExpressionList()) {
			boolean expCh = e.accept(this);
			changed |= expCh; 
		}
		return changed;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.DestructorCall)
	 */
	@Override
	public Boolean visit(DestructorCall destrCall) {
		boolean changed = false;
		
		if(destrCall.getsName().getqName().getTypeName().equals(typeX)) {
			destrCall.getsName().getqName().setTypeName(typeToSet);
			changed = true;
		}
		
		if(destrCall.getType().equals(typeX)) {
			destrCall.setType(typeToSet);
			changed = true;
		}
		
		boolean rec = destrCall.getReceiver().accept(this); 
		changed |= rec;
		
		for(Expression e : destrCall.getExpressionList()) {
			boolean expCh = e.accept(this);
			changed |= expCh;
		}
		return changed;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.FunctionCall)
	 */
	@Override
	public Boolean visit(FunctionCall funCall) {
		boolean changed = false;
		if(funCall.getType().equals(typeX)) {
			funCall.setType(typeToSet);
			changed = true;
		}
		
		for(Expression e : funCall.getExpressions()) {
			boolean expCh = e.accept(this);
			changed |= expCh;
		}
		return changed;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.ComatchFunCall)
	 */
	@Override
	public Boolean visit(ComatchFunCall mFunCall) {
		boolean changed = false;
		if(mFunCall.getType().equals(typeX)) {
			mFunCall.setType(typeToSet);
			changed = true;
		}
		
		for(Expression e : mFunCall.getExpressionList()) {
			boolean expCh = e.accept(this);
			changed |= expCh;
		}
		return changed;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.MatchFunCall)
	 */
	@Override
	public Boolean visit(MatchFunCall cmFunCall) {
		boolean changed = false;
		if(cmFunCall.getType().equals(typeX)) {
			cmFunCall.setType(typeToSet);
			changed = true;
		}
		boolean rec = cmFunCall.getReceiver().accept(this); 
		changed |= rec;
		
		for(Expression e : cmFunCall.getExpressionList()) {
			boolean expCh = e.accept(this);
			changed |= expCh;
		}
		return changed;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.Match)
	 */
	@Override
	public Boolean visit(Match match) {
		boolean changed = false;
		if(match.getType().equals(typeX)) {
			match.setType(typeToSet);
			match.setReturnType(typeToSet);
			changed = true;
		}
		
		if(match.getqName().getTypeName().equals(typeX)) {
			match.getqName().setTypeName(typeToSet);
			changed = true;
		}
		
		changed |= match.getExpr().accept(this);
//		if(match.getReturnType().equals(typeX)) {
//			match.setReturnType(typeToSet);
//			changed = true;
//		}
		
		for(ExprDecl e : match.getExpressionDeclList()) {
			boolean expCh = e.accept(this);
			changed |= expCh;
		}
		
		for(CaseOrCocase cc : match.getBody()) {
			boolean expCh = cc.getExpr().accept(this);
			changed |= expCh;
		}
		
		return changed;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.Comatch)
	 */
	@Override
	public Boolean visit(Comatch comatch) {
		boolean changed = false;
		if(comatch.getType().equals(typeX)) {
			comatch.setType(typeToSet);
			comatch.getqName().setTypeName(typeToSet);
			changed = true;
		}
		
		for(ExprDecl e : comatch.getExpressionDeclList()) {
			boolean expCh = e.accept(this);
			changed |= expCh;
		}
		
		for(CaseOrCocase cc : comatch.getBody()) {
			boolean expCh = cc.getExpr().accept(this);
			changed |= expCh;
		}
		
		return changed;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.Let)
	 */
	@Override
	public Boolean visit(Let let) {
		boolean changed = false;
		if(let.getType().equals(typeX)) {
			let.setType(typeToSet);
			changed = true;
			
		}
		if(let.getRight().getType().equals(typeX)) {
			let.getRight().setType(typeToSet);
			changed = true;
		}
		boolean left = let.getLeft().accept(this);
		boolean right = let.getRight().accept(this);
		
		return changed || left || right;
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
		boolean changed = false;
		if(exprD.getType().equals(typeX)) {
			exprD.setType(typeToSet);
			changed = true;
		}
		
		boolean left = exprD.getLeft().accept(this);
		boolean right = exprD.getRight().accept(this);
		return changed|| left || right;
	}

}
