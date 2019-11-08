/**
 * 
 */
package de.unituebingen.decompositiondiversity.helper;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import de.unituebingen.decompositiondiversity.compiler.scope.QualifiedName;
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
import de.unituebingen.decompositiondiversity.compiler.ast.expression.MatchOrComatch;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;
import de.unituebingen.decompositiondiversity.compiler.parser.NullToken;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class InlineHelper implements ExpressionVisitor<Boolean> {
	private MatchOrComatch local;
	private String name;
	private ArrayList<Variable> vars;
	private int counter = 0;
	/**
	 * @param func
	 */
	public InlineHelper(MatchOrComatch local, String name, ArrayList<Variable> vars) {
		super();
		this.local = local;
		this.name = name;
		this.vars = vars;
	}
	
	public void setLocal(MatchOrComatch local) {
		this.local = local;
	}
	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.Variable)
	 */
	@Override
	public Boolean visit(Variable variable) {
		// Do nothing
		return false;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.ConstructorCall)
	 */
	@Override
	public Boolean visit(ConstructorCall constCall) {
		// Do nothing
		return false;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.DestructorCall)
	 */
	@Override
	public Boolean visit(DestructorCall destrCall) {
		// Do nothing
		return false;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.FunctionCall)
	 */
	@Override
	public Boolean visit(FunctionCall funCall) {
//		if(funCall.getName().equals(name)) {
//			local.setStart(funCall.getStart());
//			local.setStop(funCall.getStop());
//			
//			return true;
//		}
		return false;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.ComatchFunCall)
	 */
	@Override
	public Boolean visit(ComatchFunCall mFunCall) {
		
		if(mFunCall.getqName().getName().equals(name)) {
			if(counter > 0){
				QualifiedName qn = new QualifiedName(mFunCall.getqName().getTypeName(), name+counter);
				local.setqName(qn);
			}
			ArrayList<ExprDecl> expressions = new ArrayList<>();
			for(int i = 0;i<vars.size();++i) {
				ExprDecl exd = new ExprDecl(new NullToken(), new NullToken(), vars.get(i), mFunCall.getExpressionList().get(i), vars.get(i).getType());
				expressions.add(exd);
			}
			
			local.setStart(mFunCall.getStart());
			local.setStop(mFunCall.getStop());
			local.setExpressionDeclList(expressions);
			counter += 1;
			return true;
		}
		return false;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.MatchFunCall)
	 */
	@Override
	public Boolean visit(MatchFunCall cmFunCall) {
		
		if(cmFunCall.getqName().getName().equals(name)) {
			if(counter > 0){
				QualifiedName qn = new QualifiedName(cmFunCall.getqName().getTypeName(), name+counter);
				local.setqName(qn);
			}
			ArrayList<ExprDecl> expressions = new ArrayList<>();
			for(int i = 0;i<vars.size();++i) {
				String vName = vars.get(i).getName();
//				boolean cc = containsName(funParams,vName);
				Variable v = new Variable(vars.get(i).getStart(), vars.get(i).getStop(), vars.get(i).getType(), vName);
//				if(cc) {
//					v.setName(generateVar(funParams)); 
//				}
				
				ExprDecl exd = new ExprDecl(new NullToken(), new NullToken(), v, cmFunCall.getExpressionList().get(i), vars.get(i).getType());
				expressions.add(exd);
			}
			
			local.setStart(cmFunCall.getStart());
			local.setStop(cmFunCall.getStop());
			((Match) local).setExpr(cmFunCall.getReceiver());
			local.setExpressionDeclList(expressions);
			counter += 1;
			return true;
		}
		return false;
	}

	private boolean containsName(ArrayList<Variable> funParams2, String vName) {
		for(Variable v:funParams2) {
			if(v.getName().equals(vName))
				return true;
		}
		return false;
	}
	
	private String generateVar(ArrayList<Variable> vars) {
		StringBuilder sb = new StringBuilder();
		Random random = new Random();
		
		// returns 1, 2, through 25
        int n = random.nextInt(26);
        char value;
        do {
        	// Add 97 to move from integer to the range A to Z.
	        value = (char) (n + 97);
        }while(containsName(vars,Character.toString(value)));
        
        sb.append(value);
    
		
		return sb.toString();
	}
	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.Match)
	 */
	@Override
	public Boolean visit(Match match) {
		for(CaseOrCocase cc: match.getBody()) {
			boolean found = cc.getExpr().accept(this);
			
			if(found)
				cc.setExpr(local);
		}
		return false;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.Comatch)
	 */
	@Override
	public Boolean visit(Comatch comatch) {
		for(CaseOrCocase cc: comatch.getBody()) {
			boolean found = cc.getExpr().accept(this);
			
			if(found)
				cc.setExpr(local);
		}
		return false;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.expression.Let)
	 */
	@Override
	public Boolean visit(Let let) {
		boolean found = let.getLeft().getRight().accept(this);
		if(found)
			let.getLeft().setRight(local);
		found = let.getRight().accept(this);
		if(found)
			let.setRight(local);
		return false;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.CaseOrCocase)
	 */
	@Override
	public Boolean visit(CaseOrCocase caseOrCo) {
		// TODO Auto-generated method stub
		return false;
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.ExpressionVisitor#visit(de.unituebingen.decompositiondiversity.ast.ExprDecl)
	 */
	@Override
	public Boolean visit(ExprDecl exprD) {
		// TODO Auto-generated method stub
		return false;
	}

}
