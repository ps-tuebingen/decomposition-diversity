/**
 * 
 */
package de.unituebingen.decompositiondiversity.helper;

import de.unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase;
import de.unituebingen.decompositiondiversity.compiler.ast.Constructor;
import de.unituebingen.decompositiondiversity.compiler.ast.Destructor;
import de.unituebingen.decompositiondiversity.compiler.ast.Program;
import de.unituebingen.decompositiondiversity.compiler.ast.function.CoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.Function;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchFuction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.OneExprFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.type.CoDataType;
import de.unituebingen.decompositiondiversity.compiler.ast.type.DataType;
import de.unituebingen.decompositiondiversity.compiler.typechecker.SkeletonVisitor;

/**
 * @author Fayez Abu Alia
 *
 */
public class FunctionExtractor implements SkeletonVisitor {
	
	private ExpressionFinder expFinder;
	/**
	 * @param name
	 * @param type
	 */
	public FunctionExtractor(String name, String type) {
		super();
	
		this.expFinder = new ExpressionFinder(type, name);
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.decompositiondiversity.ast.Program)
	 */
	@Override
	public void visit(Program program) {
		for(Function fun: program.getFunctionDeclerations()) {
			fun.accept(this);
		}
		
		if(expFinder.getExtractedFunction() != null) {
			program.getFunctionDeclerations().add(0, expFinder.getExtractedFunction());
		}
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.decompositiondiversity.ast.type.DataType)
	 */
	@Override
	public void visit(DataType dataType) {
		// Do nothing

	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.decompositiondiversity.ast.type.CoDataType)
	 */
	@Override
	public void visit(CoDataType codataType) {
		// Do nothing

	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.decompositiondiversity.ast.Constructor)
	 */
	@Override
	public void visit(Constructor constr) {
		// Do nothing

	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.decompositiondiversity.ast.Destructor)
	 */
	@Override
	public void visit(Destructor destr) {
		// Do nothing

	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.decompositiondiversity.ast.function.OneExprFunction)
	 */
	@Override
	public void visit(OneExprFunction function) {
		boolean found = function.getBody().accept(expFinder);
		
		if(found) {
			function.setBody(expFinder.getReplacementExp());
		}
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.decompositiondiversity.ast.function.MatchFuction)
	 */
	@Override
	public void visit(MatchFuction function) {
		for(CaseOrCocase cc : function.getBody()) {
			boolean found = cc.getExpr().accept(expFinder);
			if(found) {
				cc.setExpr(expFinder.getReplacementExp());
			}
		}
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.decompositiondiversity.ast.function.CoMatchFunction)
	 */
	@Override
	public void visit(CoMatchFunction function) {
		for(CaseOrCocase cc : function.getBody()) {
			boolean found = cc.getExpr().accept(expFinder);
			if(found) {
				cc.setExpr(expFinder.getReplacementExp());
			}
		}

	}

}
