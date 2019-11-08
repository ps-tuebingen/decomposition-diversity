/**
 * 
 */
package de.unituebingen.decompositiondiversity.helper;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import de.unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase;
import de.unituebingen.decompositiondiversity.compiler.ast.Program;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Comatch;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Match;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.MatchOrComatch;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;
import de.unituebingen.decompositiondiversity.compiler.ast.function.CoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.Function;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchFuction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchOrCoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.OneExprFunction;
import de.unituebingen.decompositiondiversity.compiler.environment.Environment;
import de.unituebingen.decompositiondiversity.compiler.parser.NullToken;
import de.unituebingen.decompositiondiversity.compiler.parser.ASTGenerator.ASTGenerator;
import de.unituebingen.decompositiondiversity.compiler.parser.ASTGenerator.BodiesGenerator;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityLexer;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.ProgContext;
import de.unituebingen.decompositiondiversity.compiler.parser.exception.NotDeclaredException;
import de.unituebingen.decompositiondiversity.compiler.parser.exception.RefactoringNotAvaliable;
import de.unituebingen.decompositiondiversity.compiler.parser.exception.DecompositionDiversityException;
import de.unituebingen.decompositiondiversity.compiler.scope.QualifiedName;
import de.unituebingen.decompositiondiversity.compiler.typechecker.SkeletonChecker;

/**
 * @author Fayez Abu Alia
 *
 */
public class ASTWorker {
	/**
	 * Generates AST from source code.
	 * 
	 * @param src the source code to be translated to AST
	 * @return the generated AST
	 *  @throws IOException  If an input or output 
	 *				         exception occurred
	 */
	public Program generator(String src) throws IOException {
		
		InputStream stream = new ByteArrayInputStream(src.getBytes(StandardCharsets.UTF_8));
		DecompositionDiversityLexer lexer = new DecompositionDiversityLexer(CharStreams.fromStream(stream, StandardCharsets.UTF_8));
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		DecompositionDiversityParser parser = new DecompositionDiversityParser(tokens);
		
		ProgContext progCtx = parser.prog();
		
		ASTGenerator gen = new ASTGenerator();
		Program pr = gen.convertProgram(progCtx);
		
		BodiesGenerator bg = new BodiesGenerator(gen.getEnv(),progCtx);
        bg.generate();
        
        SkeletonChecker sc = new SkeletonChecker(gen.getEnv());
        sc.visit(pr);
        
        return pr;
	}
	/**
	 * Extracts a co-/match function from a local co-/match.
	 * @param type the type of the expression ("match" or "comatch")
	 * @param localName the name of comatch 
	 * @param ast the abstract syntax tree
	 * 
	 * @return the modified ast that has the extracted co-/match function.
	 * 			All co-/match's with localName will be replaced by the call of the extracted
	 * 			co-/match function
	 */
	public Program extractFunc(String type, String localName, Program ast, Environment env) {
		if(env.lookUp(localName))
			throw new RefactoringNotAvaliable("Extract function is not avaliable on types");
		
		try {
			env.getFunction(localName);
			throw new RefactoringNotAvaliable("Extract function is not avaliable on functions");
		} catch (NotDeclaredException e) {
			try {
				env.getConsOrDes(type,localName);
				throw new RefactoringNotAvaliable("Extract function is not avaliable on Constructors/Destructors");
			} catch (NotDeclaredException e1) {
				FunctionExtractor funExtractor = new FunctionExtractor(localName, type);
				ast.accept(funExtractor);
				return ast;
			}
		}
		
	}
	
	/**
	 * Replace a co-/match function call with corresponding co-/match expression.
	 * 
	 * @param funName the name of function 
	 * @param ast the abstract syntax tree
	 * @param env compile environment
	 * 
	 * @return the modified ast.
	 * 			All co-/match function call's with funName will be replaced by corresponding
	 * 			co-/match expression.
	 */
	public Program inlineFunc(String funName, Program ast, Environment env) {
		try {
			Function fun = env.getFunction(funName);
			RecursiveCallFinder finder = new RecursiveCallFinder(funName);
			if(fun instanceof OneExprFunction)
				throw new RefactoringNotAvaliable("Inline is not avaliable on function " + funName);
			for(CaseOrCocase cc : ((MatchOrCoMatchFunction) fun).getBody()) {
				if(cc.getExpr().accept(finder))
					throw new RefactoringNotAvaliable("Inline is not avaliable on function " + funName);
			}
			
			boolean isMatch = fun instanceof MatchFuction;
			MatchOrComatch local = generateLocalMatchOrComatch(isMatch,fun);
//			if(fun instanceof MatchFuction) {
//				Match match = new Match(new NullToken(), new NullToken(), ((MatchFuction) fun).getReceiverType(), ((MatchFuction) fun).getqName(), null, null, ((MatchFuction) fun).getBody(), fun.getReturnType());
//				local = match;
//			} else if(fun instanceof CoMatchFunction) {
//				Comatch comatch = new Comatch(new NullToken(), new NullToken(), fun.getReturnType(), ((CoMatchFunction) fun).getqName() , null, ((CoMatchFunction) fun).getBody());
//				local = comatch;
//			}
			InlineHelper helper = new InlineHelper(local, funName, fun.getArguments());
			for(Function f : ast.getFunctionDeclerations()) {
				if(f instanceof OneExprFunction) {
					boolean found = ((OneExprFunction) f).getBody().accept(helper);
					if(found) {
						((OneExprFunction) f).setBody(local);
						local = generateLocalMatchOrComatch(isMatch, fun);
						helper.setLocal(local);
					}
				} else if(f instanceof MatchFuction) {
					for(CaseOrCocase cc: ((MatchFuction) f).getBody()) {
						boolean found = cc.getExpr().accept(helper);
						
						if(found) {
							cc.setExpr(local);
							local = generateLocalMatchOrComatch(isMatch, fun);
							helper.setLocal(local);
						}
					}
				} else if(f instanceof CoMatchFunction) {
					
					for(CaseOrCocase cc: ((CoMatchFunction) f).getBody()) {
						
						boolean found = cc.getExpr().accept(helper);
						
						if(found) {
							cc.setExpr(local);
							local = generateLocalMatchOrComatch(isMatch, fun);
							helper.setLocal(local);
						}
					}
				}
				
			}
			Function toRemove = null;
			for(Function f : ast.getFunctionDeclerations()) {
				if(!(f instanceof OneExprFunction)) {
					MatchOrCoMatchFunction mcf = (MatchOrCoMatchFunction) f;
					if(mcf.getqName().getName().equals(funName))
						toRemove = f;
				}
			}
			boolean isRemoved = ast.getFunctionDeclerations().remove(toRemove);
			
			if(!isRemoved)
				throw new DecompositionDiversityException(funName + "is NOT removed.");
			
			return ast;
		} catch (Exception e) {
			e.printStackTrace();
			throw e;
		}
		
	}
	private MatchOrComatch generateLocalMatchOrComatch(boolean isMatch, Function fun) {
		QualifiedName qn;
		if(isMatch) {
			qn = ((MatchFuction) fun).getqName();
//			String newName = "_"+qn.getName();
//			qn.setName(newName);
			Match match = new Match(new NullToken(), new NullToken(), ((MatchFuction) fun).getReceiverType(), qn, null, null, ((MatchFuction) fun).getBody(), fun.getReturnType());
			return match;
		} else {
			qn = ((CoMatchFunction) fun).getqName();
//			String newName = "_"+qn.getName();
//			qn.setName(newName);
			Comatch comatch = new Comatch(new NullToken(), new NullToken(), fun.getReturnType(), qn , null, ((CoMatchFunction) fun).getBody());
			return comatch;
		}
	}
}
