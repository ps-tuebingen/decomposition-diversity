/**
 * 
 */
package de.unituebingen.decompositiondiversity.helper;

import java.util.ArrayList;

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
import de.unituebingen.decompositiondiversity.compiler.ast.function.CoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.Function;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchFuction;
import de.unituebingen.decompositiondiversity.compiler.parser.NullToken;
import de.unituebingen.decompositiondiversity.compiler.parser.exception.RefactoringNotAvaliable;
import de.unituebingen.decompositiondiversity.compiler.scope.QualifiedName;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class ExpressionFinder implements ExpressionVisitor<Boolean> {
	private String expType;
	private String name;
	private Expression replacementExp;
	private Function extractedFunction;
	
	/**
	 * @param expType
	 */
	public ExpressionFinder(String expType, String name) {
		super();
		this.expType = expType;
		this.name = name;
	}
	
	public Expression getReplacementExp() {
		return replacementExp;
	}
	
	public Function getExtractedFunction() {
		return extractedFunction;
	}
	
	@Override
	public Boolean visit(Variable variable) {
		if(variable.getName().equals(name))
			throw new RefactoringNotAvaliable("Extract function is not avaliable on variables");
		
		return false;
	}

	@Override
	public Boolean visit(ConstructorCall constCall) {
		if(constCall.getsName().getqName().getName().equals(name))
			throw new RefactoringNotAvaliable("Extract function is not avaliable on constructor call " + name);

		int pos = 0;
		ArrayList<Integer> allPos = new ArrayList<>();
		for(Expression ex:constCall.getExpressionList()) {
			boolean found = ex.accept(this);
			if(found)
				allPos.add(pos);
			++pos;
		}
		
		for(int p : allPos) {
			constCall.getExpressionList().remove(p);
			constCall.getExpressionList().add(p, replacementExp);
		}
		
		return false;
	}

	@Override
	public Boolean visit(DestructorCall destrCall) {
		if(destrCall.getsName().getqName().getName().equals(name))
			throw new RefactoringNotAvaliable("Extract function is not avaliable on destructor call " + name);

		int pos = 0;
		ArrayList<Integer> allPos = new ArrayList<>();
		for(Expression ex:destrCall.getExpressionList()) {
			boolean found = ex.accept(this);
			if(found)
				allPos.add(pos);
			++pos;
		}
		
		for(int p : allPos) {
			destrCall.getExpressionList().remove(p);
			destrCall.getExpressionList().add(p, replacementExp);
		}

		return false;
	}

	@Override
	public Boolean visit(FunctionCall funCall) {
		if(funCall.getName().equals(name))
			throw new RefactoringNotAvaliable("Extract function is not avaliable on function call " + name);
		
		int pos = 0;
		ArrayList<Integer> allPos = new ArrayList<>();
		for(Expression ex:funCall.getExpressions()) {
			boolean found = ex.accept(this);
			if(found)
				allPos.add(pos);
			++pos;
		}
		
		for(int p : allPos) {
			funCall.getExpressions().remove(p);
			funCall.getExpressions().add(p, replacementExp);
		}
		return false;
	}

	@Override
	public Boolean visit(ComatchFunCall mFunCall) {
		if(mFunCall.getqName().getName().equals(name))
			throw new RefactoringNotAvaliable("Extract function is not avaliable on comatch function call " + name);
		int pos = 0;
		ArrayList<Integer> allPos = new ArrayList<>();
		for(Expression ex:mFunCall.getExpressionList()) {
			boolean found = ex.accept(this);
			if(found)
				allPos.add(pos);
			++pos;
		}
		
		for(int p : allPos) {
			mFunCall.getExpressionList().remove(p);
			mFunCall.getExpressionList().add(p, replacementExp);
		}
		
		return false;
	}

	@Override
	public Boolean visit(MatchFunCall cmFunCall) {
		if(cmFunCall.getqName().getName().equals(name))
			throw new RefactoringNotAvaliable("Extract function is not avaliable on match function call " + name);
		if(cmFunCall.getReceiver().accept(this))
			cmFunCall.setReceiver(replacementExp);
		
		int pos = 0;
		ArrayList<Integer> allPos = new ArrayList<>();
		for(Expression ex:cmFunCall.getExpressionList()) {
			boolean found = ex.accept(this);
			if(found)
				allPos.add(pos);
			++pos;
		}
		
		for(int p : allPos) {
			cmFunCall.getExpressionList().remove(p);
			cmFunCall.getExpressionList().add(p, replacementExp);
		}
		return false;
	}

	@Override
	public Boolean visit(Match match) {
		if(expType.equals("comatch") && match.getqName().getName().equals(name)) {
			throw new RefactoringNotAvaliable("Extract comatch function is not avaliable on match expressions");
		}
		
		if(expType.equals("match") && /*match.getqName().getTypeName().equals(typename) &&*/ 
				match.getqName().getName().equals(name)) {
			
			if(replacementExp == null) {
				QualifiedName qn = match.getqName();
				qn.setName(name.substring(1));
				ArrayList<Expression> args = new ArrayList<>();
				for(ExprDecl ex:match.getExpressionDeclList()) {
					args.add(ex.getRight());
				}
				replacementExp = new MatchFunCall(match.getStart(), match.getStop(), 
						match.getType(), qn, args, match.getExpr());
				
				ArrayList<Variable> vars = new ArrayList<>();
				for(ExprDecl ex:match.getExpressionDeclList()) {
					vars.add(ex.getLeft());
				}
				
				extractedFunction = new MatchFuction(new NullToken(), new NullToken(), 
						match.getExpr().getType(), qn, vars, match.getReturnType(), 
						match.getBody(), new ArrayList<>());
			}
			
			return true;
		} else {
//			boolean found = false;
			for(CaseOrCocase cc : match.getBody()) {
				
				boolean found = cc.getExpr().accept(this);
				
				if(found) {
					cc.setExpr(replacementExp);
				}
			}
			
			return false;
		}
	}

	@Override
	public Boolean visit(Comatch comatch) {
		if(expType.equals("match") && comatch.getqName().getName().equals(name)) {
			throw new RefactoringNotAvaliable("Extract match function is not avaliable on comatch expressions");
		}
		
		if(expType.equals("comatch") && comatch.getqName().getName().equals(name)) {
			if(replacementExp == null) {
				QualifiedName qn = comatch.getqName();
				qn.setName(name.substring(1));
				ArrayList<Expression> args = new ArrayList<>();
				for(ExprDecl ex:comatch.getExpressionDeclList()) {
					args.add(ex.getRight());
				}
				replacementExp = new ComatchFunCall(comatch.getStart(), comatch.getStop(), 
						comatch.getType(), qn, args);
				
				ArrayList<Variable> vars = new ArrayList<>();
				for(ExprDecl ex:comatch.getExpressionDeclList()) {
					vars.add(ex.getLeft());
				}
				
				extractedFunction = new CoMatchFunction(new NullToken(), new NullToken(), qn, 
						vars, comatch.getType(), comatch.getBody(), new ArrayList<>());
			}
			
			return true;
		} else {
//			boolean found = false;
			for(CaseOrCocase cc : comatch.getBody()) {
				boolean found = cc.getExpr().accept(this);
				
				if(found) {
					cc.setExpr(replacementExp);
				}
			}
			
			return false;
		}
	}

	@Override
	public Boolean visit(Let let) {
		boolean found = let.getLeft().getRight().accept(this);
		if(found)
			let.getLeft().setRight(replacementExp);
		
		found = let.getRight().accept(this);
		if(found)
			let.setRight(replacementExp);
		
		return false; 
	}

	@Override
	public Boolean visit(CaseOrCocase caseOrCo) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Boolean visit(ExprDecl exprD) {
		// TODO Auto-generated method stub
		return null;
	}

}
