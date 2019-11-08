/**
 * 
 */
package de.unituebingen.decompositiondiversity.helper;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

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
import de.unituebingen.decompositiondiversity.compiler.ast.expression.MatchOrComatchFunCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;
import de.unituebingen.decompositiondiversity.compiler.scope.QualifiedName;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class VariableReplacer implements ExpressionVisitor<Boolean> {
	private final QualifiedName qn;
	private final String type;
	private final List<Expression> expList;
	private final boolean isMatchFunCall;

	private final List<Variable> vars;

	/**
	 * @param mFunCall
	 * @param cmFunCall
	 */
	public VariableReplacer(QualifiedName qn, String type, List<Expression> expList, boolean isMatchFunCall,
			List<Variable> vars) {
		super();
		this.qn = qn;
		this.type = type;
		this.expList = expList;
		this.isMatchFunCall = isMatchFunCall;
		
		this.vars = vars;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.Variable)
	 */
	@Override
	public Boolean visit(Variable variable) {
		// TODO Auto-generated method stub
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
		boolean replaced = false;
		Map<Integer, Expression> posAndFunCallMap = new HashMap<>();

		for (int i = 0; i < constCall.getExpressionList().size(); ++i) {
			Expression e = constCall.getExpressionList().get(i);
			if (e instanceof Variable) {
				if (inVars((Variable) e)) {
					if (isMatchFunCall) {
						MatchFunCall revTransCall = new MatchFunCall(e.getStart(), e.getStop(), type, qn, expList, e);
						posAndFunCallMap.put(i, revTransCall);
					} else {
						//TODO
					}
				}
			} else {
				e.accept(this);
			}
		}
		return null;
	}

	private boolean inVars(Variable e) {
		for (Variable v : vars) {
			if (v.getName().equals(e.getName()))
				return true;
		}
		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.DestructorCall)
	 */
	@Override
	public Boolean visit(DestructorCall destrCall) {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.FunctionCall)
	 */
	@Override
	public Boolean visit(FunctionCall funCall) {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.ComatchFunCall)
	 */
	@Override
	public Boolean visit(ComatchFunCall mFunCall) {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.MatchFunCall)
	 */
	@Override
	public Boolean visit(MatchFunCall cmFunCall) {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.Match)
	 */
	@Override
	public Boolean visit(Match match) {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.Comatch)
	 */
	@Override
	public Boolean visit(Comatch comatch) {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.expression.Let)
	 */
	@Override
	public Boolean visit(Let let) {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase)
	 */
	@Override
	public Boolean visit(CaseOrCocase caseOrCo) {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor#visit(de.
	 * unituebingen.decompositiondiversity.compiler.ast.ExprDecl)
	 */
	@Override
	public Boolean visit(ExprDecl exprD) {
		// TODO Auto-generated method stub
		return null;
	}

}
