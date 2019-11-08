/**
 * 
 */
package de.unituebingen.decompositiondiversity.helper;

import java.util.ArrayList;
import java.util.List;

import de.unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase;
import de.unituebingen.decompositiondiversity.compiler.ast.ExprDecl;
import de.unituebingen.decompositiondiversity.compiler.ast.Program;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Comatch;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.ComatchFunCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.ConstructorCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.DestructorCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.FunctionCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Let;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Match;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.MatchFunCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.MatchOrComatch;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.MatchOrComatchFunCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;
import de.unituebingen.decompositiondiversity.compiler.ast.function.Function;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchOrCoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.OneExprFunction;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class MatchComatchFinder implements ExpressionVisitor<Boolean> {
	
	private final List<MatchOrComatch> all = new ArrayList<>();
	private final String type;
	// did not use bool isMatch, because imported modules are type correct
	// therefore typename of match can not be typename of comatch
	/**
	 * @param ast
	 * @param isMatch
	 */
	public MatchComatchFinder(List<Function> functions, String type) {
		super();
		this.type = type;
		
		for(Function f: functions) {
			if(f instanceof OneExprFunction) {
				((OneExprFunction) f).getBody().accept(this);
			} else {
				if(f instanceof MatchOrCoMatchFunction) {
					for(CaseOrCocase cc : ((MatchOrCoMatchFunction) f).getBody()) {
						cc.getExpr().accept(this);
					}
				}
			}
		}
	}
	
	public List<MatchOrComatch> getAll() {
		return all;
	}
	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable)
	 */
	@Override
	public Boolean visit(Variable variable) {
		return false;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.compiler.ast.expression.ConstructorCall)
	 */
	@Override
	public Boolean visit(ConstructorCall constCall) {
		// TODO Auto-generated method stub
		return false;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.compiler.ast.expression.DestructorCall)
	 */
	@Override
	public Boolean visit(DestructorCall destrCall) {
		// TODO Auto-generated method stub
		return false;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.compiler.ast.expression.FunctionCall)
	 */
	@Override
	public Boolean visit(FunctionCall funCall) {
		// TODO Auto-generated method stub
		return false;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.compiler.ast.expression.ComatchFunCall)
	 */
	@Override
	public Boolean visit(ComatchFunCall mFunCall) {
		// TODO Auto-generated method stub
		return false;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.compiler.ast.expression.MatchFunCall)
	 */
	@Override
	public Boolean visit(MatchFunCall cmFunCall) {
		
		return false;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.compiler.ast.expression.Match)
	 */
	@Override
	public Boolean visit(Match match) {
		boolean has = false;
		if(match.getqName().getTypeName().equals(type)) {
			all.add(match);
			has = true;
		}
		for(CaseOrCocase cc : match.getBody()) {
			has |= cc.getExpr().accept(this);
		}
		return has;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.compiler.ast.expression.Comatch)
	 */
	@Override
	public Boolean visit(Comatch comatch) {
		boolean has = false;
		if(comatch.getqName().getTypeName().equals(type)) {
			all.add(comatch);
			has = true;
		}
		for(CaseOrCocase cc : comatch.getBody()) {
			has |= cc.getExpr().accept(this);
		}
		return has;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.compiler.ast.expression.Let)
	 */
	@Override
	public Boolean visit(Let let) {
		boolean left = let.getLeft().getRight().accept(this);
		boolean right = let.getRight().accept(this);
		return  left || right;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase)
	 */
	@Override
	public Boolean visit(CaseOrCocase caseOrCo) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.compiler.ast.ExprDecl)
	 */
	@Override
	public Boolean visit(ExprDecl exprD) {
		// TODO Auto-generated method stub
		return null;
	}

}
