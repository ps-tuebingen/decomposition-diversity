/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler.parser.ASTGenerator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

import de.unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase;
import de.unituebingen.decompositiondiversity.compiler.ast.Constructor;
import de.unituebingen.decompositiondiversity.compiler.ast.ConstructorOrDestructor;
import de.unituebingen.decompositiondiversity.compiler.ast.Destructor;
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
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchOrCoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.OneExprFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.type.CoDataType;
import de.unituebingen.decompositiondiversity.compiler.ast.type.DataType;
import de.unituebingen.decompositiondiversity.compiler.environment.Environment;
import de.unituebingen.decompositiondiversity.compiler.parser.NullToken;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.CaseStmtContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.CocaseContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.ComatchContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.ComatchExprContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.GenCallExprContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.ConsumerFunBodyContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.DefContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.ExprDeclContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.ExpressionContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.ExpressionDeclListContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.ExpressionListContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.FunBodyContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.FunCallExprContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.GeneratorFunBodyContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.LambdaExprContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.LetContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.LetExprContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.MatchContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.MatchExprContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.ConsCallExprContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.NatContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.ProgContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.VarExprContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.VarListContext;
import de.unituebingen.decompositiondiversity.compiler.parser.error.DuplicateNameException;
import de.unituebingen.decompositiondiversity.compiler.parser.error.Error;
import de.unituebingen.decompositiondiversity.compiler.parser.error.Error.ErrorSeverity;
import de.unituebingen.decompositiondiversity.compiler.parser.error.ErrorFactory;
import de.unituebingen.decompositiondiversity.compiler.parser.exception.NotDeclaredException;
import de.unituebingen.decompositiondiversity.compiler.parser.exception.DecompositionDiversityException;
import de.unituebingen.decompositiondiversity.compiler.parser.exception.WrongArgumentsNumber;
import de.unituebingen.decompositiondiversity.compiler.parser.exception.LookupErr;
import de.unituebingen.decompositiondiversity.compiler.scope.MODIFIER;
import de.unituebingen.decompositiondiversity.compiler.scope.QualifiedName;
import de.unituebingen.decompositiondiversity.compiler.scope.ScopedName;

/**
 * @author Fayez Abu Alia
 *
 */
public class BodiesGenerator {
	public static final String X = "$X$";
	private final Environment env;
	private final List<Error> errors = new ArrayList<>();
	private final ProgContext progCtx;
	private Map<String, List<Variable>> localVarsCase;
	private boolean inCC = false;
	private String cccName = "";

	/**
	 * @param env
	 * @param errors
	 */
	public BodiesGenerator(Environment env, ProgContext progCtx) {
		this.env = env;
		this.progCtx = progCtx;
	}

	public List<Error> getErrors() {
		return errors;
	}

	public Environment getEnv() {
		return env;
	}

	public int getNumOfErrors() {
		int r = 0;
		for (Error e : errors) {
			if (e.getErrSev() == ErrorSeverity.ERROR)
				++r;
		}
		return r;
	}

	public void generate() {

		for (DefContext def : progCtx.def()) {
			if (def.functionDeclarations() != null) {
				String name;
				try {
					localVarsCase = new HashMap<>();
					if (def.functionDeclarations().functionDecl() != null) {
						name = def.functionDeclarations().functionDecl().functionHeader().name.getText();
						Function fun = env.getFunction(name, Environment.OEXFUNCTION);
						generateFunBody(name, fun, def.functionDeclarations().functionDecl().funBody());
					} else if (def.functionDeclarations().consumerFunctionDecl() != null) {
						name = def.functionDeclarations().consumerFunctionDecl().consumerFunHeader().name.getText();
						Function fun = env.getFunction(name, Environment.CONSFUNCTION);
						generateConsFunBody(name, fun,
								def.functionDeclarations().consumerFunctionDecl().consumerFunBody());

					} else if (def.functionDeclarations().generatorFunctionDecl() != null) {
						name = def.functionDeclarations().generatorFunctionDecl().generatorFunHeader().name.getText();
						Function fun = env.getFunction(name, Environment.GENFUNCTION);
						generateConsFunBody(name, fun,
								def.functionDeclarations().generatorFunctionDecl().generatorFunBody());
					}

				} catch (DecompositionDiversityException e) {
					e.printStackTrace();
				}

			}
		}

	}

	private void generateConsFunBody(String name, Function fun, GeneratorFunBodyContext generatorFunBody)
			throws DecompositionDiversityException {
		List<CaseOrCocase> body = new ArrayList<>();

		for (CocaseContext ccs : generatorFunBody.cocase()) {
			CaseOrCocase cc = convertCoCase(ccs, fun);
			body.add(cc);
		}
		if (body.isEmpty()) {
			String msg = "No cocases are declared for generator function " + name;
			Error warn = ErrorFactory.createWarning(fun.getStart().getLine(), fun.getStop().getLine(),
					fun.getStart().getCharPositionInLine(), fun.getStop().getCharPositionInLine(), msg);

			errors.add(warn);
		}
		((CoMatchFunction) fun).setBody(body);
	}

	private void generateConsFunBody(String name, Function fun, ConsumerFunBodyContext consumerFunBody)
			throws DecompositionDiversityException {
		List<CaseOrCocase> body = new ArrayList<>();

		for (CaseStmtContext cs : consumerFunBody.caseStmt()) {
			CaseOrCocase cc = convertCase(cs, fun, ((MatchFuction) fun).getReceiverType());
			body.add(cc);
		}
		if (body.isEmpty()) {
			String msg = "No cases are declared for consumer function " + name;
			Error warn = ErrorFactory.createWarning(fun.getStart().getLine(), fun.getStop().getLine(),
					fun.getStart().getCharPositionInLine(), fun.getStop().getCharPositionInLine(), msg);

			errors.add(warn);
		}
		((MatchFuction) fun).setBody(body);
	}

	private void generateFunBody(String name, Function fun, FunBodyContext funBody) throws DecompositionDiversityException {
		ExpressionContext ex = funBody.expression();

		Expression expression = ConvertExpression(ex, fun, 0);
		((OneExprFunction) fun).setBody(expression);

	}

	private Variable convertVarExpr(VarExprContext var, Function fun) throws DecompositionDiversityException {
		String type = lookUp(var.var.getText(), fun);
		if (type == null) {
			int sLine = var.var.getLine();
			int eLine = var.var.getLine();
			int sCol = var.getStart().getCharPositionInLine();
			int eCol = var.getStop().getCharPositionInLine();

			String msg = "Variable " + var.var.getText() + " is not declared.";

			Error err = ErrorFactory.createError(sLine, eLine, sCol, eCol, msg);
			errors.add(err);

			throw new NotDeclaredException(msg);
		}

		return new Variable(var.getStart(), var.getStop(), type, var.var.getText());

	}

	private ConstructorCall convertConstrCall(GenCallExprContext constrCall, Function fun, int level)
			throws DecompositionDiversityException, LookupErr {
		int line = constrCall.ogenCall.getStart().getLine();
		int startCol = constrCall.ogenCall.getStart().getCharPositionInLine();
		int stopCol = constrCall.ogenCall.getStop().getCharPositionInLine();
		String name = constrCall.ogenCall.name.getText();

        try {
            env.lookUpConstrCall(name);
        } catch (DecompositionDiversityException e) {
            String msg = "Constructor " + name + " is not declared.";
            throw new LookupErr(msg);
        }
		ScopedName sName;

		try {
			sName = env.lookUpConstrCall(name);
		} catch (NotDeclaredException e2) {
			Error err = ErrorFactory.createError(line, line, startCol, stopCol, e2.getMessage());
			errors.add(err);
			throw e2;
		}catch (DecompositionDiversityException e) {
			MODIFIER mod = name.contains("_") ? MODIFIER.LOCAL : MODIFIER.GLOBAL;
			String funName;
			if (fun instanceof OneExprFunction) {
				funName = ((OneExprFunction) fun).getName();
			} else {
				funName = ((MatchOrCoMatchFunction) fun).getqName().getName();
			}
			sName = new ScopedName(mod, new QualifiedName(funName + "$" + name + "$" + level + X, name));
		} 

		List<Expression> exprList = new ArrayList<>();
		if (constrCall.ogenCall.expressionList() != null) {
			getExprList(constrCall.ogenCall.expressionList(), exprList, fun, level);
		}

		ConstructorCall cCall = new ConstructorCall(constrCall.getStart(), constrCall.getStop(),
				sName.getqName().getTypeName(), sName, exprList);

		if (sName.getqName().getTypeName().contains(X))
			env.getExprWithTypeX().add(cCall);

		return cCall;

	}

	private void getExprList(ExpressionListContext expressionList, List<Expression> exprList, Function fun, int level)
			throws DecompositionDiversityException {
		++level;
		if (expressionList.expressionList() == null) {
			Expression expr = ConvertExpression(expressionList.expression(), fun, level);

			exprList.add(expr);
		} else {
			getExprList(expressionList.expressionList(), exprList, fun, level);

			Expression expr = ConvertExpression(expressionList.expression(), fun, level);

			exprList.add(expr);
		}

	}

	private Expression ConvertExpression(ExpressionContext expression, Function fun, int level)
			throws DecompositionDiversityException {
		if (expression instanceof NatContext) {
			NatContext number = (NatContext) expression;
			return convertNumber(number, fun);

		} else if (expression instanceof VarExprContext) {
			VarExprContext var = (VarExprContext) expression;
			return convertVarExpr(var, fun);

		} else if (expression instanceof GenCallExprContext) {
			GenCallExprContext genCall = (GenCallExprContext) expression;

			try {
                return convertConstrCall(genCall, fun, level);
            } catch (LookupErr e) {
                return convertCMFunCall(genCall, fun);
            }

		} else if (expression instanceof ConsCallExprContext) {
			ConsCallExprContext consCall = (ConsCallExprContext) expression;

			try {
                return convertDestrCall(consCall, fun, level);
            } catch (LookupErr e) {
                return convertMatchFunCall(consCall, fun);
            }

		} else if (expression instanceof FunCallExprContext) {
			FunCallExprContext funCall = (FunCallExprContext) expression;

			return convertFunCall(funCall, fun);

		} else if (expression instanceof MatchExprContext) {
			MatchExprContext match = (MatchExprContext) expression;

			return convertMatch(match.matchExpr, fun);

		} else if (expression instanceof ComatchExprContext) {
			ComatchExprContext comatch = (ComatchExprContext) expression;

			return convertCoMatch(comatch.comatchExpr, fun);
		} else if (expression instanceof LambdaExprContext) {
			LambdaExprContext lambda = (LambdaExprContext) expression;

			return convertLambda(lambda, fun);
		} else {
			// let expression
			LetExprContext let = (LetExprContext) expression;

			return convertLet(let.let(), fun);
		}
	}

	private Expression convertLambda(LambdaExprContext lambda, Function fun) {
		Token token = new NullToken();
		Expression rightSide = ConvertExpression(lambda.lambda().expression(), fun, 0);
		String returnType = rightSide.getType();

		String lsType = lambda.lambda().type.getText();

		String typeName = lsType + "To" + returnType;

		ScopedName sn = new ScopedName(MODIFIER.GLOBAL, new QualifiedName(typeName, "apply"));
		ArrayList<String> typeNames = new ArrayList<>();
		typeNames.add(lsType);
		Destructor des = new Destructor(token, token, sn, typeNames, returnType);

		List<ConstructorOrDestructor> body = new ArrayList<>();
		body.add(des);
		CoDataType newType = new CoDataType(token, typeName, body);
		env.getContext().put(typeName, newType);
		env.getGeneratedTypes().add(newType);

		QualifiedName qnComatch = new QualifiedName(typeName, "_lambda");

		Variable v = new Variable(lambda.getStart(), lambda.getStop(), lsType, lambda.lambda().var.getText());
		List<Variable> params = new ArrayList<>();
		params.add(v);

		CaseOrCocase cocase = new CaseOrCocase(lambda.getStart(), lambda.getStop(), sn, params, rightSide);
		List<CaseOrCocase> cmBody = new ArrayList<>();
		cmBody.add(cocase);

		List<ExprDecl> expressionDeclList = new ArrayList<>();
		VariablesGetter getter = new VariablesGetter(fun.getLocalVars(), expressionDeclList);
		rightSide.accept(getter);

		Comatch comatch = new Comatch(lambda.getStart(), lambda.getStop(), typeName, qnComatch, expressionDeclList,
				cmBody);
		return comatch;
	}

	private Expression convertNumber(NatContext number, Function fun) throws DecompositionDiversityException {
		int line = number.getStart().getLine();
		int startCol = number.getStart().getCharPositionInLine();
		int stopCol = number.getStart().getCharPositionInLine();

		if (!env.lookUp("Nat")) {
			String msg = "Type Nat is not declared.";
			Error err = ErrorFactory.createError(line, line, startCol, stopCol, msg);
			errors.add(err);
			throw new NotDeclaredException(msg);
		}

		String name;
		int n = Integer.parseInt(number.NATNUM().getText());
		List<Expression> exprList = new ArrayList<>();
		if (n == 0) {
			name = "Zero";
			if (env.lookUpConstrCall(name) == null) {
				String msg = "Constructor Zero is not declared.";
				Error err = ErrorFactory.createError(line, line, startCol, stopCol, msg);
				errors.add(err);
				throw new NotDeclaredException(msg);
			}

		} else {
			name = "Succ";
			if (env.lookUpConstrCall(name) == null) {
				String msg = "Constructor Succ is not declared.";
				Error err = ErrorFactory.createError(line, line, startCol, stopCol, msg);
				errors.add(err);
				throw new NotDeclaredException(msg);
			}

			ConstructorCall cc = convertNumToCons(number.getStart(), number.getStop(), n - 1);
			exprList.add(cc);
		}

		ScopedName sName = env.lookUpConstrCall(name);

		return new ConstructorCall(number.getStart(), number.getStop(), sName.getqName().getTypeName(), sName,
				exprList);
	}

	private ConstructorCall convertNumToCons(Token start, Token stop, int n) {
		if (n == 0) {
			String name = "Zero";
			List<Expression> exprList = new ArrayList<>();
			ScopedName sName = env.lookUpConstrCall(name);
			return new ConstructorCall(start, stop, sName.getqName().getTypeName(), sName, exprList);
		} else {
			String name = "Succ";
			List<Expression> exprList = new ArrayList<>();
			ScopedName sName = env.lookUpConstrCall(name);
			ConstructorCall cc = convertNumToCons(start, stop, n - 1);
			exprList.add(cc);

			return new ConstructorCall(start, stop, sName.getqName().getTypeName(), sName, exprList);
		}
	}

	private Expression convertLet(LetContext let, Function fun) throws DecompositionDiversityException {
		String varName = let.assignVar().name.getText();
		if (hasLocal(fun, let.assignVar().name.getText())) {
			String msg = "Variable " + varName + " is already declared and cannot be declared twice.";
			Error err = ErrorFactory.createError(let.assignVar().name.getLine(), let.assignVar().name.getLine(),
					let.assignVar().name.getCharPositionInLine(),
					let.assignVar().name.getCharPositionInLine() + varName.length(), msg);
			errors.add(err);
			throw new DuplicateNameException(msg);
		}

		Expression exp = ConvertExpression(let.assignVar().expression(), fun, 0);

		Variable var = new Variable(let.assignVar().start, let.assignVar().getStop(), exp.getType(), varName);
		fun.getLocalVars().add(var);

		ExprDecl exDecl = new ExprDecl(let.start, let.assignVar().getStop(), var, exp, exp.getType());

		Expression right = ConvertExpression(let.expression(), fun, 0);

		Let letExpr = new Let(let.getStart(), let.getStop(), right.getType(), exDecl, right);
		if (exp.getType().contains(X) || right.getType().contains(X)) {
			env.getExprWithTypeX().add(letExpr);
		}
		return letExpr;

	}

	private Expression convertCoMatch(ComatchContext comatchExpr, Function fun) throws DecompositionDiversityException {
		String name = comatchExpr.name.getText();
		String typeName = (comatchExpr.type != null) ? comatchExpr.type.getText() : X + name;

		// change to get type and check if it is a datatype pr codatatype!
		if (typeName.contains(X) || (env.getType(typeName) != null && (env.getType(typeName) instanceof CoDataType))) {
			if (!env.lookUpFunctionName(name)) {
				List<ExprDecl> exprList = new ArrayList<>();
				if (comatchExpr.expressionDeclList() != null) {
					getExprDeclList(comatchExpr.expressionDeclList(), exprList, fun, new ArrayList<>());

				}

				List<CaseOrCocase> body = new ArrayList<>();
				boolean b = !typeName.contains(X);

				int numOfCases = 0;

				if (b)
					numOfCases = env.getType(typeName).getBody().size();

				int i = 0;

				for (CocaseContext ccas : comatchExpr.cocase()) {
					if (b && i >= numOfCases) {
						break;
					}
					++i;
					CaseOrCocase cc = convertCoCaseLocal(ccas, typeName, fun, exprList);
					if (cc != null)
						body.add(cc);
				}
				if (body.isEmpty()) {
					String msg = "No cocases are declared for comatch expression " + name;
					Error warn = ErrorFactory.createWarning(comatchExpr.getStart().getLine(), comatchExpr.getStop().getLine(),
							comatchExpr.getStart().getCharPositionInLine(), comatchExpr.getStop().getCharPositionInLine(), msg);

					errors.add(warn);
				}
				boolean hasTypeX = false;
				for (ExprDecl ed : exprList) {
					if (ed.getType().contains(X)) {
						hasTypeX = true;
						break;
					}
				}
				Comatch comatch = new Comatch(comatchExpr.getStart(), comatchExpr.getStop(), typeName,
						new QualifiedName(typeName, name), exprList, body);

				if (typeName.contains(X) || hasTypeX)
					env.getExprWithTypeX().add(comatch);

				// remove local variables of comatch from local variable list of fun
				for (ExprDecl exd : exprList) {
					fun.getLocalVars().remove(exd.getLeft());
				}

				return comatch;

			} else {
				String msg = "Function " + name + " is already declared and cannot be declared twice.";
				Error err = ErrorFactory.createError(comatchExpr.name.getLine(), comatchExpr.name.getLine(),
						comatchExpr.name.getCharPositionInLine(),
						comatchExpr.name.getCharPositionInLine() + name.length(), msg);
				errors.add(err);

				throw new DuplicateNameException(msg);
			}

		} else {
			String msg = "Type " + typeName + " is not declared.";
			Error err = ErrorFactory.createError(comatchExpr.type.getLine(), comatchExpr.type.getLine(),
					comatchExpr.type.getCharPositionInLine(),
					comatchExpr.type.getCharPositionInLine() + typeName.length(), msg);
			errors.add(err);
			throw new NotDeclaredException(msg);
		}

	}

	// ccLvl case/cocase level to ignore copying the declared variables from the
	// previous
	// case/cocase level
	private CaseOrCocase convertCoCase(CocaseContext ccas, Function fun) throws DecompositionDiversityException {
		inCC = true;
		String destName = ccas.cocaseDestr().name.getText();
		cccName = destName;
		ConstructorOrDestructor des = null;
		try {
			des = env.getConsOrDes(fun.getReturnType(), destName, false);
			if (des instanceof Constructor) {
				String msg = "Destructor " + ccas.cocaseDestr().name.getText() + " is not declared";
				Error err = ErrorFactory.createError(ccas.cocaseDestr().name.getLine(),
						ccas.cocaseDestr().name.getLine(), ccas.cocaseDestr().getStart().getCharPositionInLine(),
						ccas.cocaseDestr().getStop().getCharPositionInLine(), msg);
				errors.add(err);
				throw new NotDeclaredException(msg);
			}

		} catch (DecompositionDiversityException e) {
			// TODO: handle exception
		}

		List<Variable> varList = new ArrayList<>();
		if (ccas.cocaseDestr().varList() != null) {
//			getVarList(ccas.cocaseDestr().varList(), varList, des, 0, fun, ccas);
			getVars(ccas.cocaseDestr().varList(), varList);
			try {
				checkVarList(varList, fun, des);
				localVarsCase.put(destName, varList);
			} catch (WrongArgumentsNumber e) {
				Error err = ErrorFactory.createError(ccas.cocaseDestr().getStart().getLine(),
						ccas.cocaseDestr().getStop().getLine(), ccas.cocaseDestr().getStart().getCharPositionInLine(),
						ccas.cocaseDestr().getStop().getCharPositionInLine(), e.getMessage());
				errors.add(err);
			}
//			localVarsCase.put(destName, varList);
		}

		// if (des != null && des.getTypeNames().size() == varList.size()) {
		Expression ex = ConvertExpression(ccas.expression(), fun, 0);
		if (ex.getType().contains(X) && !env.getExprWithTypeX().contains(ex))
			env.getExprWithTypeX().add(ex);

		inCC = false;
		ScopedName sn;

		MODIFIER mod = destName.contains("_") ? MODIFIER.LOCAL : MODIFIER.GLOBAL;
		if (des == null) {
			sn = new ScopedName(mod, new QualifiedName(fun.getReturnType(), destName));
		} else {
			sn = des.getsName();
		}

		if (sn.getqName().getTypeName().contains(X))
			env.getConsDesWithTypeX().add(sn);
		return new CaseOrCocase(ccas.getStart(), ccas.getStop(), sn, varList, ex);

//		} else {
//			String msg = "Number of arguments does not match definition.";
//			Error err = ErrorFactory.createError(ccas.cocaseDestr().getStart().getLine(),
//					ccas.cocaseDestr().getStop().getLine(), ccas.cocaseDestr().getStart().getCharPositionInLine(),
//					ccas.cocaseDestr().getStop().getCharPositionInLine(), msg);
//			errors.add(err);
//			throw new WrongArgumentsNumber(msg);
//		}

	}

	private CaseOrCocase convertCoCaseLocal(CocaseContext ccas, String type, Function fun, List<ExprDecl> exprList)
			throws DecompositionDiversityException {
		inCC = true;
		String destName = ccas.cocaseDestr().name.getText();
		cccName = destName;
		ConstructorOrDestructor des = null;
		try {
//			des = env.getConsOrDes(fun.getReturnType(), destName, false);
			des = env.getConsOrDes(type, destName, false);
			if (des instanceof Constructor) {
				String msg = "Destructor " + ccas.cocaseDestr().name.getText() + " is not declared";
				Error err = ErrorFactory.createError(ccas.cocaseDestr().name.getLine(),
						ccas.cocaseDestr().name.getLine(), ccas.cocaseDestr().getStart().getCharPositionInLine(),
						ccas.cocaseDestr().getStop().getCharPositionInLine(), msg);
				errors.add(err);
				throw new NotDeclaredException(msg);
			}

		} catch (DecompositionDiversityException e) {
			// TODO: handle exception
		}

		List<Variable> varList = new ArrayList<>();
		if (ccas.cocaseDestr().varList() != null) {
//			getVarList(ccas.cocaseDestr().varList(), varList, des, 0, fun, ccas);
			getVars(ccas.cocaseDestr().varList(), varList);
			try {
				checkVarList(varList, fun, des);
				localVarsCase.put(destName, varList);
			} catch (WrongArgumentsNumber e) {
				Error err = ErrorFactory.createError(ccas.cocaseDestr().getStart().getLine(),
						ccas.cocaseDestr().getStop().getLine(), ccas.cocaseDestr().getStart().getCharPositionInLine(),
						ccas.cocaseDestr().getStop().getCharPositionInLine(), e.getMessage());
				errors.add(err);
			}
//			localVarsCase.put(destName, varList);
		}

		// if (des != null && des.getTypeNames().size() == varList.size()) {
		Expression ex = ConvertExpression(ccas.expression(), fun, 0);

		List<Variable> allVars = new ArrayList<>(fun.getLocalVars());
		VariablesGetter getter = new VariablesGetter(allVars, exprList);
		ex.accept(getter);

		if (ex.getType().contains(X) && !env.getExprWithTypeX().contains(ex))
			env.getExprWithTypeX().add(ex);

		inCC = false;
		ScopedName sn;

		MODIFIER mod = destName.contains("_") ? MODIFIER.LOCAL : MODIFIER.GLOBAL;
		if (des == null) {
			sn = new ScopedName(mod, new QualifiedName(fun.getReturnType(), destName));
		} else {
			sn = des.getsName();
		}

		if (sn.getqName().getTypeName().contains(X))
			env.getConsDesWithTypeX().add(sn);
		return new CaseOrCocase(ccas.getStart(), ccas.getStop(), sn, varList, ex);

//		} else {
//			String msg = "Number of arguments does not match definition.";
//			Error err = ErrorFactory.createError(ccas.cocaseDestr().getStart().getLine(),
//					ccas.cocaseDestr().getStop().getLine(), ccas.cocaseDestr().getStart().getCharPositionInLine(),
//					ccas.cocaseDestr().getStop().getCharPositionInLine(), msg);
//			errors.add(err);
//			throw new WrongArgumentsNumber(msg);
//		}

	}

	private Expression convertMatch(MatchContext matchExpr, Function fun) throws DecompositionDiversityException {
		String name = matchExpr.name.getText();
		String typeName = matchExpr.type != null ? matchExpr.type.getText() : X + name;

		if (typeName.contains(X) || env.getType(typeName) != null && (env.getType(typeName) instanceof DataType)) {

			if (!env.lookUpFunctionName(name)) {
				Expression exp = ConvertExpression(matchExpr.expression(), fun, 0);

				List<ExprDecl> exprList = new ArrayList<>();
				if (matchExpr.expressionDeclList() != null) {
					getExprDeclList(matchExpr.expressionDeclList(), exprList, fun, new ArrayList<>());
				}

				String returnType = matchExpr.rt != null ? matchExpr.rt.getText() : name + X;
				boolean b = !typeName.contains(X);

				int numOfCases = 0;

				if (b)
					numOfCases = env.getType(typeName).getBody().size();

				List<CaseOrCocase> body = new ArrayList<>();
				int i = 0;
				for (CaseStmtContext cas : matchExpr.caseStmt()) {
					if (b && i >= numOfCases) {
						break;
					}
					++i;
//					CaseOrCocase cc = convertCase(cas, fun, typeName);
					CaseOrCocase cc = convertCaseLocal(cas, fun, exprList, typeName);
					if (cc != null)
						body.add(cc);
				}
				if (body.isEmpty()) {
					String msg = "No cases are declared for match expression " + name;
					Error warn = ErrorFactory.createWarning(matchExpr.getStart().getLine(), matchExpr.getStop().getLine(),
							matchExpr.getStart().getCharPositionInLine(), matchExpr.getStop().getCharPositionInLine(), msg);

					errors.add(warn);
				}
				Match match = new Match(matchExpr.getStart(), matchExpr.getStop(), returnType,
						new QualifiedName(typeName, name), exp, exprList, body, returnType);

				boolean hasTypeX = false;
				for (ExprDecl ed : exprList) {
					if (ed.getType().contains(X)) {
						hasTypeX = true;
						break;
					}
				}

				if (typeName.contains(X) || returnType.contains(X) || hasTypeX)
					env.getExprWithTypeX().add(match);

				// remove local variables of comatch from local variable list of fun
				for (ExprDecl exd : exprList) {
					fun.getLocalVars().remove(exd.getLeft());
				}

				return match;

			} else {
				String msg = "Function " + name + " is already declared and can not be declared twice.";
				Error err = ErrorFactory.createError(matchExpr.name.getLine(), matchExpr.name.getLine(),
						matchExpr.name.getCharPositionInLine(), matchExpr.name.getCharPositionInLine() + name.length(),
						msg);
				errors.add(err);

				throw new DuplicateNameException(msg);
			}
		} else {
			String msg = "Datatype " + typeName + " is not declared.";
			Error err = ErrorFactory.createError(matchExpr.type.getLine(), matchExpr.type.getLine(),
					matchExpr.type.getCharPositionInLine(), matchExpr.type.getCharPositionInLine() + typeName.length(),
					msg);
			errors.add(err);
			throw new NotDeclaredException(msg);
		}
	}

	private CaseOrCocase convertCaseLocal(CaseStmtContext cas, Function fun, List<ExprDecl> exprList, String typeName) {
		inCC = true;

		String constName = cas.caseConst().name.getText();
		cccName = constName;
		ConstructorOrDestructor cons = null;
		try {
			cons = env.getConsOrDes(typeName, constName, true);
			if (cons == null || (cons instanceof Destructor)) {
				String msg = "Constructor " + constName + " is not declared.";
				int startPos = cas.caseConst().name.getCharPositionInLine();
				Error err = ErrorFactory.createError(cas.caseConst().name.getLine(), cas.caseConst().name.getLine(),
						startPos, startPos + cas.caseConst().name.getText().length(), msg);
				errors.add(err);
				throw new NotDeclaredException(msg);
			}

		} catch (DecompositionDiversityException e) {
			// TODO: handle exception
		}
		List<Variable> varList = new ArrayList<>();
		if (cas.caseConst().varList() != null) {
			getVars(cas.caseConst().varList(), varList);
//			getVarList(cas.caseConst().varList(), varList, cons, 0, fun, cas);
			try {
				checkVarList(varList, fun, cons);
				localVarsCase.put(constName, varList);
			} catch (WrongArgumentsNumber e) {
				Error err = ErrorFactory.createError(cas.caseConst().getStart().getLine(),
						cas.caseConst().getStop().getLine(), cas.caseConst().getStart().getCharPositionInLine(),
						cas.caseConst().getStop().getCharPositionInLine(), e.getMessage());
				errors.add(err);
			}

		}

//		if (cons.getTypeNames().size() == varList.size()) {
		Expression ex = ConvertExpression(cas.expression(), fun, 0);

		List<Variable> allVars = new ArrayList<>(fun.getLocalVars());
		VariablesGetter getter = new VariablesGetter(allVars, exprList);
		ex.accept(getter);

		if (ex.getType().contains(X) && !env.getExprWithTypeX().contains(ex))
			env.getExprWithTypeX().add(ex);

		inCC = false;
		MODIFIER mod = constName.contains("_") ? MODIFIER.LOCAL : MODIFIER.GLOBAL;
		ScopedName sn;
		if (cons == null) {
			sn = new ScopedName(mod, new QualifiedName(typeName, constName));
		} else {
			sn = cons.getsName();
		}
		if (sn.getqName().getTypeName().contains(X)) {
			env.getConsDesWithTypeX().add(sn);
		}
		return new CaseOrCocase(cas.getStart(), cas.getStop(), sn, varList, ex);

//		} else {
//			String msg = "Number of arguments does not match definition";
//			int startPos = cas.caseConst().start.getCharPositionInLine();
//			Error err = ErrorFactory.createError(cas.caseConst().getStart().getLine(),
//					cas.caseConst().getStop().getLine(), startPos, cas.caseConst().getStop().getCharPositionInLine(),
//					msg);
//			errors.add(err);
//			throw new WrongArgumentsNumber("Constructor " + constName + ": " + msg);
//		}
	}

	private CaseOrCocase convertCase(CaseStmtContext cas, Function fun, String typeName) throws DecompositionDiversityException {
		inCC = true;

		String constName = cas.caseConst().name.getText();
		cccName = constName;
		ConstructorOrDestructor cons = null;
		try {
			cons = env.getConsOrDes(typeName, constName, true);
			if (cons == null || (cons instanceof Destructor)) {
				String msg = "Constructor " + constName + " is not declared.";
				int startPos = cas.caseConst().name.getCharPositionInLine();
				Error err = ErrorFactory.createError(cas.caseConst().name.getLine(), cas.caseConst().name.getLine(),
						startPos, startPos + cas.caseConst().name.getText().length(), msg);
				errors.add(err);
				throw new NotDeclaredException(msg);
			}

		} catch (DecompositionDiversityException e) {
			// TODO: handle exception
		}
		List<Variable> varList = new ArrayList<>();
		if (cas.caseConst().varList() != null) {
			getVars(cas.caseConst().varList(), varList);
//			getVarList(cas.caseConst().varList(), varList, cons, 0, fun, cas);
			try {
				checkVarList(varList, fun, cons);
				localVarsCase.put(constName, varList);
			} catch (WrongArgumentsNumber e) {
				Error err = ErrorFactory.createError(cas.caseConst().getStart().getLine(),
						cas.caseConst().getStop().getLine(), cas.caseConst().getStart().getCharPositionInLine(),
						cas.caseConst().getStop().getCharPositionInLine(), e.getMessage());
				errors.add(err);
			}

		}

//		if (cons.getTypeNames().size() == varList.size()) {
		Expression ex = ConvertExpression(cas.expression(), fun, 0);
		if (ex.getType().contains(X) && !env.getExprWithTypeX().contains(ex))
			env.getExprWithTypeX().add(ex);

		inCC = false;
		MODIFIER mod = constName.contains("_") ? MODIFIER.LOCAL : MODIFIER.GLOBAL;
		ScopedName sn;
		if (cons == null) {
			sn = new ScopedName(mod, new QualifiedName(typeName, constName));
		} else {
			sn = cons.getsName();
		}
		if (sn.getqName().getTypeName().contains(X)) {
			env.getConsDesWithTypeX().add(sn);
		}
		return new CaseOrCocase(cas.getStart(), cas.getStop(), sn, varList, ex);

//		} else {
//			String msg = "Number of arguments does not match definition";
//			int startPos = cas.caseConst().start.getCharPositionInLine();
//			Error err = ErrorFactory.createError(cas.caseConst().getStart().getLine(),
//					cas.caseConst().getStop().getLine(), startPos, cas.caseConst().getStop().getCharPositionInLine(),
//					msg);
//			errors.add(err);
//			throw new WrongArgumentsNumber("Constructor " + constName + ": " + msg);
//		}
	}

	private void checkVarList(List<Variable> varList, Function fun, ConstructorOrDestructor cons) {
		boolean sameArgNum = true;
		for (Variable v : varList) {
			int sl = v.getStart().getLine();
			int stl = v.getStop().getLine();
			int sc = v.getStart().getCharPositionInLine();
			int stc = v.getStop().getCharPositionInLine();

			if (hasLocalVar(fun.getLocalVars(), v.getName())) {
				String msg = "Variable " + v.getName() + " is already declared and can not declared twice.";
				Error err = ErrorFactory.createError(sl, stl, sc, stc, msg);
				errors.add(err);

				throw new DuplicateNameException(msg);

			}

			if (cons != null && sameArgNum) {
				if (cons.getTypeNames().size() == varList.size()) {
					int pos = varList.indexOf(v);
					String type = cons.getTypeNames().get(pos);
					v.setType(type);
				} else {
					sameArgNum = false;
					String msg = "Number of arguments of " + cons.getsName().getqName().getName()
							+ " does not match with its decleration.";

					throw new WrongArgumentsNumber(msg);
				}
			} else if (cons == null) {
				env.getExprWithTypeX().add(v);
			}
		}

	}

	private void getVars(VarListContext varListCtx, List<Variable> varList) {
		if (varListCtx.varList() == null) {
			String name = varListCtx.name.getText();
			String vType = name + X;
			Variable v = new Variable(varListCtx.getStart(), varListCtx.getStop(), vType, name);
			varList.add(v);
		} else {
			getVars(varListCtx.varList(), varList);

			String name = varListCtx.name.getText();
			String vType = name + X;
			Variable v = new Variable(varListCtx.getStart(), varListCtx.getStop(), vType, name);
			varList.add(v);

		}
	}

	private void getVarList(VarListContext varListCtx, List<Variable> varList, ConstructorOrDestructor cons,
			int posInConsParams, Function fun, ParserRuleContext pcas) throws DecompositionDiversityException {

		ArrayList<String> vars = new ArrayList<>();

		if (varListCtx.varList() == null) {
			String name = varListCtx.name.getText();
			if (hasLocalVar(fun.getLocalVars(), name)) {
				String msg = "Variable " + name + " is already declared and can not declared twice.";
				int startPos = varListCtx.name.getCharPositionInLine();
				Error err = ErrorFactory.createError(varListCtx.name.getLine(), varListCtx.name.getLine(), startPos,
						startPos + varListCtx.name.getText().length(), msg);
				errors.add(err);

				throw new DuplicateNameException(msg);
			} // else {
			if (cons != null && vars.size() == cons.getTypeNames().size()) {
				int sLine;
				int eLine;
				int startPos;
				int ePos;
				if (cons instanceof Constructor) {
					CaseStmtContext cas = (CaseStmtContext) pcas;
					sLine = cas.caseConst().getStart().getLine();
					eLine = cas.caseConst().getStop().getLine();
					startPos = cas.caseConst().getStart().getCharPositionInLine();
					ePos = cas.caseConst().getStop().getCharPositionInLine();
				} else {
					CocaseContext ccas = (CocaseContext) pcas;
					sLine = ccas.cocaseDestr().getStart().getLine();
					eLine = ccas.cocaseDestr().getStop().getLine();
					startPos = ccas.cocaseDestr().getStart().getCharPositionInLine();
					ePos = ccas.cocaseDestr().getStop().getCharPositionInLine();
				}
				String msg = "Number of arguments of " + cons.getsName().getqName().getName()
						+ " does not match with its decleration.";

				Error err = ErrorFactory.createError(sLine, eLine, startPos, ePos, msg);
				errors.add(err);
				throw new WrongArgumentsNumber(msg);
			}
			String vType = cons == null ? name + X
					: cons.getTypeNames().get(cons.getTypeNames().size() - 1 - posInConsParams);
			Variable v = new Variable(varListCtx.getStart(), varListCtx.getStop(), vType, name);
			varList.add(v);
			vars.add(name);
			if (vType.contains(X))
				env.getExprWithTypeX().add(v);

		} else {
			getVarList(varListCtx.varList(), varList, cons, ++posInConsParams, fun, pcas);

			String name = varListCtx.name.getText();
			if (hasLocalVar(fun.getLocalVars(), name)) {
				int startPos = varListCtx.name.getCharPositionInLine();
				String msg = "Variable " + name + " is already declared and can not declared twice.";
				Error err = ErrorFactory.createError(varListCtx.name.getLine(), varListCtx.name.getLine(), startPos,
						startPos + varListCtx.name.getText().length(), msg);
				errors.add(err);
				throw new DuplicateNameException(msg);
			}
			if (cons != null && vars.size() == cons.getTypeNames().size()) {
				int sLine;
				int eLine;
				int startPos;
				int ePos;
				if (cons instanceof Constructor) {
					CaseStmtContext cas = (CaseStmtContext) pcas;
					sLine = cas.caseConst().getStart().getLine();
					eLine = cas.caseConst().getStop().getLine();
					startPos = cas.caseConst().getStart().getCharPositionInLine();
					ePos = cas.caseConst().getStop().getCharPositionInLine();
				} else {
					CocaseContext ccas = (CocaseContext) pcas;
					sLine = ccas.cocaseDestr().getStart().getLine();
					eLine = ccas.cocaseDestr().getStop().getLine();
					startPos = ccas.cocaseDestr().getStart().getCharPositionInLine();
					ePos = ccas.cocaseDestr().getStop().getCharPositionInLine();
				}
				String msg = "Number of arguments of " + cons.getsName().getqName().getName()
						+ " does not match with its decleration.";

				Error err = ErrorFactory.createError(sLine, eLine, startPos, ePos, msg);
				errors.add(err);
				throw new WrongArgumentsNumber(msg);
			}
			String vType = cons == null ? name + X
					: cons.getTypeNames().get(cons.getTypeNames().size() - 1 - posInConsParams);
			Variable v = new Variable(varListCtx.getStart(), varListCtx.getStop(), vType, name);
			varList.add(v);
			vars.add(name);
			if (vType.contains(X))
				env.getExprWithTypeX().add(v);
		}

	}

	private boolean hasLocalVar(ArrayList<Variable> localVars, String name) {
		for (Variable v : localVars) {
			if (v.getName().equals(name))
				return true;
		}

		return false;
	}

	private void getExprDeclList(ExpressionDeclListContext expressionDeclList, List<ExprDecl> exprList, Function fun,
			ArrayList<String> vars) throws DecompositionDiversityException {

		if (expressionDeclList.expressionDeclList() == null) {
			ExprDecl expr = ConvertExprDecl(expressionDeclList.exprDecl(), fun, vars);

			exprList.add(expr);
		} else {
			getExprDeclList(expressionDeclList.expressionDeclList(), exprList, fun, vars);
			ExprDecl expr = ConvertExprDecl(expressionDeclList.exprDecl(), fun, vars);

			exprList.add(expr);
		}

	}

	private ExprDecl ConvertExprDecl(ExprDeclContext exprDecl, Function fun, ArrayList<String> vars)
			throws DecompositionDiversityException {
		Expression right = ConvertExpression(exprDecl.assignVar().expression(), fun, 0);

//		if (hasLocal(fun, exprDecl.assignVar().name.getText())) {
//			String msg = "Local variable " + exprDecl.assignVar().name.getText()
//					+ " is already declared and cannot be declared twice.";
//			Error err = ErrorFactory.createError(exprDecl.assignVar().name.getLine(),
//					exprDecl.assignVar().name.getLine(), exprDecl.assignVar().name.getCharPositionInLine(),
//					exprDecl.assignVar().name.getCharPositionInLine() + exprDecl.assignVar().name.getText().length(),
//					msg);
//			errors.add(err);
//			throw new DuplicateNameException(msg);
//		} else {

		String varName = exprDecl.assignVar().name.getText();

		String t = exprDecl.type != null ? exprDecl.type.getText() : right.getType();

		Variable var = new Variable(exprDecl.assignVar().getStart(), exprDecl.assignVar().getStart(), t, varName);

		vars.add(varName);
		fun.getLocalVars().add(var);

		ExprDecl ed = new ExprDecl(exprDecl.getStart(), exprDecl.getStop(), var, right, t);

		if (right.getType().contains(X)) {
			env.getExprWithTypeX().add(right);
			// env.getExprWithTypeX().add(var);
		}
		return ed;
//		}

	}

	private boolean hasLocal(Function fun, String text) {
		for (Variable v : fun.getLocalVars()) {
			if (v.getName().equals(text)) {
				return true;
			}
		}
		return false;
	}

	private Expression convertMatchFunCall(ConsCallExprContext funCall, Function fun) {
		Expression receiver = ConvertExpression(funCall.expression(), fun, 0);
		String name = funCall.consCall.getText();
		try {
			MatchFuction f = (MatchFuction) env.getFunction(name);
			QualifiedName qName = f.getqName();

			List<Expression> exprList = new ArrayList<>();
			if (funCall.expressionList() != null) {
				getExprList(funCall.expressionList(), exprList, fun, 0);
			}
			if (f.getArguments().size() != exprList.size()) {
				String msg = "Number of arguments does not match definition";

				Error err = ErrorFactory.createError(funCall.getStart().getLine(), funCall.getStop().getLine(),
						funCall.getStart().getCharPositionInLine(), funCall.getStop().getCharPositionInLine(), msg);
				errors.add(err);
				throw new DecompositionDiversityException(msg);
			} else {
				MatchFunCall mFunCall = new MatchFunCall(funCall.getStart(), funCall.getStop(), f.getReturnType(),
						qName, exprList, receiver);

				if (receiver.getType().contains(X) || f.getReturnType().contains(X))
					env.getExprWithTypeX().add(mFunCall);

				return mFunCall;

			}

		} catch (DecompositionDiversityException e) {
			String msg = e.getMessage();
			Error err = ErrorFactory.createError(funCall.consCall.getLine(), funCall.consCall.getLine(),
					funCall.consCall.getCharPositionInLine(), funCall.consCall.getCharPositionInLine() + name.length(),
					msg);
			errors.add(err);
			throw e;
		}

	}

	private Expression convertCMFunCall(GenCallExprContext funCall, Function fun) {

		String name = funCall.ogenCall.name.getText();
		try {
			CoMatchFunction f = (CoMatchFunction) env.getFunction(name, Environment.GENFUNCTION);
			QualifiedName qName = f.getqName();

			List<Expression> exprList = new ArrayList<>();
			if (funCall.ogenCall.expressionList() != null) {
				getExprList(funCall.ogenCall.expressionList(), exprList, fun, 0);
			}

			return new ComatchFunCall(funCall.getStart(), funCall.getStop(), f.getReturnType(), qName, exprList);

		} catch (Exception e) {
			String msg = e.getMessage();
			Error err = ErrorFactory.createError(funCall.ogenCall.name.getLine(), funCall.ogenCall.name.getLine(),
					funCall.ogenCall.name.getCharPositionInLine(),
					funCall.ogenCall.name.getCharPositionInLine() + name.length(), msg);
			errors.add(err);
			throw e;
		}

	}

	private Expression convertFunCall(FunCallExprContext funCall, Function fun) {
		String name = funCall.ofunCall.name.getText();
		try {
			String type = env.lookUpFunType(name);
			List<Expression> exprList = new ArrayList<>();
			if (funCall.ofunCall.expressionList() != null) {
				getExprList(funCall.ofunCall.expressionList(), exprList, fun, 0);
			}

			FunctionCall funCallExpr = new FunctionCall(funCall.getStart(), funCall.getStop(), type, name, exprList);

			if (type.contains(X))
				env.getExprWithTypeX().add(funCallExpr);

			return funCallExpr;
		} catch (DecompositionDiversityException e) {
			String msg = e.getMessage();
			Error err = ErrorFactory.createError(funCall.ofunCall.name.getLine(), funCall.ofunCall.name.getLine(),
					funCall.ofunCall.name.getCharPositionInLine(),
					funCall.ofunCall.name.getCharPositionInLine() + name.length(), msg);
			errors.add(err);
			throw e;
		}

	}

	private Expression convertDestrCall(ConsCallExprContext destrCall, Function fun, int level)
			throws DecompositionDiversityException, LookupErr {
		Expression receiver = ConvertExpression(destrCall.expression(), fun, 0);

//		if (env.lookUpDestrCall(destrCall.destName.getText()) == null) {
//			int line = destrCall.destName.getLine();
//			int startCol = destrCall.destName.getCharPositionInLine();
//			String name = destrCall.destName.getText();
//			int stopCol = startCol + name.length();
//
//			String msg = "Destructor " + name + " is not declared";
//			Error err = ErrorFactory.createError(line, line, startCol, stopCol, msg);
//			errors.add(err);
//
//			throw new NotDeclaredException(msg);
//		} else {
		int line = destrCall.consCall.getLine();
		int startCol = destrCall.consCall.getCharPositionInLine();
		String name = destrCall.consCall.getText();
        int stopCol = startCol + name.length();
		ScopedName sName;
		String returnType;

        //if (env.lookUpDestrCall(name) == null) {
        try {
            env.lookUpDestrCall(name);
        } catch (DecompositionDiversityException e) {
            String msg = "Destructor " + name + " is not declared.";
            throw new LookupErr(msg);
        }

		try {
			Destructor des = env.lookUpDestrCall(name);
			sName = des.getsName();
			returnType = des.getReturnType();
		} catch (DecompositionDiversityException e) {
			MODIFIER mod = name.contains("_") ? MODIFIER.LOCAL : MODIFIER.GLOBAL;
			String funName;
			if (fun instanceof OneExprFunction) {
				funName = ((OneExprFunction) fun).getName();
			} else {
				funName = ((MatchOrCoMatchFunction) fun).getqName().getName();
			}
			sName = new ScopedName(mod, new QualifiedName(X + receiver.getType() + "$" + name + "$" + funName, name));
			returnType = funName + "$" + receiver.getType() + "$" + name + X;
		}

		List<Expression> exprList = new ArrayList<>();
		if (destrCall.expressionList() != null) {
			getExprList(destrCall.expressionList(), exprList, fun, 0);
		}
		DestructorCall desCall = new DestructorCall(destrCall.getStart(), destrCall.getStop(), returnType, sName,
				exprList, receiver);
		if (receiver.getType().contains(X))
			env.getExprWithTypeX().add(desCall);
		if (returnType.contains(X) || sName.getqName().getTypeName().contains(X))
			env.getExprWithTypeX().add(desCall);
		return desCall;
//		}

	}

	private String lookUp(String name, Function fun) {
		for (Variable var : fun.getLocalVars()) {
			if (name.equals(var.getName()))
				return var.getType();
		}
		if (inCC && localVarsCase.keySet().contains(cccName)) {
			for (Variable v : localVarsCase.get(cccName)) {
				if (name.equals(v.getName()))
					return v.getType();
			}

		}
		return null;
	}

}
