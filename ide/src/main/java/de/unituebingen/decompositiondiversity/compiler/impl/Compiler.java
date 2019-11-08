/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler.impl;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.List;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.json.JSONArray;

import com.fasterxml.jackson.databind.ObjectMapper;

import de.unituebingen.decompositiondiversity.compiler.ICompiler;
import de.unituebingen.decompositiondiversity.compiler.ast.Program;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Expression;
import de.unituebingen.decompositiondiversity.compiler.ast.function.CoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.Function;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchFuction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.OneExprFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.type.CoDataType;
import de.unituebingen.decompositiondiversity.compiler.ast.type.DataType;
import de.unituebingen.decompositiondiversity.compiler.ast.type.Type;
import de.unituebingen.decompositiondiversity.compiler.environment.HasTypeX;
import de.unituebingen.decompositiondiversity.compiler.json.JSONGenerator;
import de.unituebingen.decompositiondiversity.compiler.parser.ASTGenerator.ASTGenerator;
import de.unituebingen.decompositiondiversity.compiler.parser.ASTGenerator.BodiesGenerator;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityLexer;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.ProgContext;
import de.unituebingen.decompositiondiversity.compiler.parser.error.Error;
import de.unituebingen.decompositiondiversity.compiler.parser.error.ErrorFactory;
import de.unituebingen.decompositiondiversity.compiler.parser.error.SyntaxError;
import de.unituebingen.decompositiondiversity.compiler.parser.error.SyntaxErrorListener;
import de.unituebingen.decompositiondiversity.compiler.parser.error.Error.ErrorSeverity;
import de.unituebingen.decompositiondiversity.compiler.typechecker.SkeletonChecker;
import de.unituebingen.decompositiondiversity.helper.Config;
import de.unituebingen.decompositiondiversity.helper.Constants;
import de.unituebingen.decompositiondiversity.message.response.CompilerResponse;

/**
 * @author Fayez Abu Alia
 *
 */
public class Compiler implements ICompiler {

	@Override
	public CompilerResponse compile(String prog) throws IOException {
		Config.datatypes = new JSONArray();
		Config.codatatypes = new JSONArray();
		
		CompilerResponse res = new CompilerResponse();
		SyntaxErrorListener errorListener = new SyntaxErrorListener();
		int numOfErr = 0;
		JSONArray warnings = new JSONArray();
		
		InputStream stream = new ByteArrayInputStream(prog.getBytes(StandardCharsets.UTF_8));
		DecompositionDiversityLexer lexer = new DecompositionDiversityLexer(CharStreams.fromStream(stream, StandardCharsets.UTF_8));
		CommonTokenStream tokens = new CommonTokenStream(lexer);
        lexer.addErrorListener(errorListener);
		
        DecompositionDiversityParser parser = new DecompositionDiversityParser(tokens);
        parser.addErrorListener(errorListener);
		
        ProgContext progCtx = parser.prog();
        if(errorListener.getSyntaxErrors().isEmpty()) {
        	ASTGenerator gen = new ASTGenerator();
	        Program pr = gen.convertProgram(progCtx);
	        if(gen.getNumOfErrors()==0) {
	        	BodiesGenerator bg = new BodiesGenerator(gen.getEnv(),progCtx);
		        bg.generate();
		        if(bg.getNumOfErrors() == 0) {
		        	SkeletonChecker sc = new SkeletonChecker(gen.getEnv());
			        sc.visit(pr);
			        
			        if(sc.getNumOfErrors()>0) {
			        	JSONArray errs = new JSONArray();
			        	for(Error e : sc.getTypeErrors()) {
			        		errs.put(e.toJSON());
			        		if(e.getErrSev() == ErrorSeverity.ERROR)
			        			++numOfErr;
			        	}
			        	res.setStatus(Constants.ERROR);
			        	res.setResult(errs.toString());
			        } else {
			        	JSONArray errs = new JSONArray();
			        	boolean hasErr = false;
			        	for(Function function : sc.getEnv().getFunctionsWithTypeX()) {
			    			int sLine = function.getStart().getLine();
			    			int stLine = function.getStart().getLine();
			    			int sCol = function.getStart().getCharPositionInLine();
			    			int stCol = function.getStop().getCharPositionInLine();
			    			String msg = "";
			    			if(function instanceof MatchFuction) {
			    				if(((MatchFuction) function).getReceiverType().contains("$X$")){
			    					msg = "Receiver type for consumer function " + 
			    							((MatchFuction) function).getqName().getName() + " is missing.";
			    				}
			    				if(function.getReturnType().contains("$X$")){
			    					msg = "Return type for consumer function " + 
			    							((MatchFuction) function).getqName().getName() + " is missing.";
			    				}
			    			} else {
			    				if(function instanceof CoMatchFunction) {
			    					msg = "Return type for generator function " + 
			    							((CoMatchFunction) function).getqName().getName() + " is missing.";
			    				} else {
			    					msg = "Return type for function " + 
			    							((OneExprFunction) function).getName() + " is missing.";
			    				}
			    			}
			    			
			    			Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
			    			errs.put(err.toJSON());
			    			hasErr = true;
			    			++numOfErr;
			    		}
			        	for(Expression ex:sc.getEnv().getExprWithTypeX()) {
			        		if(ex.accept(new HasTypeX())) {
			        			int sLine = ex.getStart().getLine();
				    			int stLine = ex.getStart().getLine();
				    			int sCol = ex.getStart().getCharPositionInLine();
				    			int stCol = ex.getStop().getCharPositionInLine();
				    			String msg = "Type of this expression is not defined";
				        		Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
				    			errs.put(err.toJSON());
				    			hasErr = true;
				    			++numOfErr;
			        		}
			        	}
			        	if(!hasErr) {
			        		// add all generated types for lambdas to AST
			        		for(Type t : sc.getEnv().getGeneratedTypes()) {
			        			pr.getTypeDeclerations().add(t);
			        		}
			        		JSONGenerator jsonGen = new JSONGenerator(pr);
			        		JSONArray jj = jsonGen.getJson();
			        		for(String t : sc.getEnv().getContext().keySet()) {
			        			if(sc.getEnv().getContext().get(t) instanceof DataType)
			        				Config.datatypes.put(t);
			        		}
			        		
			        		for(String t : sc.getEnv().getContext().keySet()) {
			        			if(sc.getEnv().getContext().get(t) instanceof CoDataType)
			        				Config.codatatypes.put(t);
			        		}
			        		
			        		addWarnings(warnings, gen.getErrors());
			        		addWarnings(warnings, bg.getErrors());
			        		addWarnings(warnings, sc.getTypeErrors());
			        		
			        		Config.env = sc.getEnv();
			        		ObjectMapper mapper = new ObjectMapper();
			        		Config.program = mapper.readValue(jj.toString(), Object.class);
			        		
			        		res.setStatus(Constants.SUCCESS);
				        	res.setResult(jj.toString());
				        	res.setEnv(sc.getEnv());
				        	
			        	} else {
			        		res.setStatus(Constants.ERROR);
				        	res.setResult(errs.toString());
				        	res.setEnv(sc.getEnv());
			        	}
			        }
		        } else {
		        	JSONArray errs = new JSONArray();
		        	for(Error e : bg.getErrors()) {
		        		errs.put(e.toJSON());
		        		if(e.getErrSev() == ErrorSeverity.ERROR)
		        			++numOfErr;
		        	}
		        	res.setStatus(Constants.ERROR);
		        	res.setResult(errs.toString());
		        	res.setEnv(bg.getEnv());
		        }
	        } else {
	        	JSONArray errs = new JSONArray();
	        	for(Error e : gen.getErrors()) {
	        		errs.put(e.toJSON());
	        		if(e.getErrSev() == ErrorSeverity.ERROR)
	        			++numOfErr;
	        	}
	        	res.setStatus(Constants.ERROR);
	        	res.setResult(errs.toString());
	        	res.setEnv(gen.getEnv());
	        }
	        
        }else {
        	JSONArray syntaxErrs = new JSONArray();
        	for(SyntaxError se : errorListener.getSyntaxErrors()) {
        		syntaxErrs.put(se.toJSON());
        		++numOfErr;
        	}
        	res.setStatus(Constants.ERROR);
        	res.setResult(syntaxErrs.toString());
        }
        res.setWarnings(warnings.toString());
        res.setNumOfErrors(numOfErr);
		return res;
	}

	/**
	 * @param warnings
	 * @param errList
	 */
	private void addWarnings(JSONArray warnings, List<Error> errList) {
		for(Error e: errList) {
			if(e.getErrSev() == ErrorSeverity.WARNING)
				warnings.put(e.toJSON());
		}
	}


}
