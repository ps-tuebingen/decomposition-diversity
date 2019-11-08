/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler.parser.ASTGenerator;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Random;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Token;
import org.json.JSONArray;
import org.json.JSONObject;

import com.fasterxml.jackson.databind.ObjectMapper;

import de.unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase;
import de.unituebingen.decompositiondiversity.compiler.ast.Constructor;
import de.unituebingen.decompositiondiversity.compiler.ast.ConstructorOrDestructor;
import de.unituebingen.decompositiondiversity.compiler.ast.Destructor;
import de.unituebingen.decompositiondiversity.compiler.ast.Import;
import de.unituebingen.decompositiondiversity.compiler.ast.Import.TRANSFORMATION;
import de.unituebingen.decompositiondiversity.compiler.ast.Program;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.ConstructorCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.DestructorCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Expression;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;
import de.unituebingen.decompositiondiversity.compiler.ast.function.CoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.Function;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchFuction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchOrCoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.OneExprFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.type.CoDataType;
import de.unituebingen.decompositiondiversity.compiler.ast.type.DataType;
import de.unituebingen.decompositiondiversity.compiler.ast.type.Type;
import de.unituebingen.decompositiondiversity.compiler.environment.Environment;
import de.unituebingen.decompositiondiversity.compiler.json.JSONGenerator;
import de.unituebingen.decompositiondiversity.compiler.linker.Linker;
import de.unituebingen.decompositiondiversity.compiler.parser.NullToken;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityLexer;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.CodataTypeDeclContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.ConstructorDeclContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.ConsumerFunctionDeclContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.DataTypeDeclContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.DefContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.DestructorDeclContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.FunctionDeclContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.GeneratorFunctionDeclContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.ImportDeclContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.ProgContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.TypeListContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.VarDeclContext;
import de.unituebingen.decompositiondiversity.compiler.parser.antlr.DecompositionDiversityParser.VarDeclListContext;
import de.unituebingen.decompositiondiversity.compiler.parser.error.DuplicateNameException;
import de.unituebingen.decompositiondiversity.compiler.parser.error.Error;
import de.unituebingen.decompositiondiversity.compiler.parser.error.Error.ErrorSeverity;
import de.unituebingen.decompositiondiversity.compiler.parser.error.ErrorFactory;
import de.unituebingen.decompositiondiversity.compiler.scope.MODIFIER;
import de.unituebingen.decompositiondiversity.compiler.scope.QualifiedName;
import de.unituebingen.decompositiondiversity.compiler.scope.ScopedName;
import de.unituebingen.decompositiondiversity.helper.Config;
import de.unituebingen.decompositiondiversity.helper.Constants;
import de.unituebingen.decompositiondiversity.message.response.ServerResponse;
import de.unituebingen.decompositiondiversity.service.CompilerService;
import de.unituebingen.decompositiondiversity.service.ConnectionService;
import de.unituebingen.decompositiondiversity.service.impl.ConnectionServiceImpl;
import de.unituebingen.decompositiondiversity.service.impl.PrettyPrintProgramServiceImpl;

/**
 * @author Fayez Abu Alia
 *
 */
public class ASTGenerator {
	private Environment env = new Environment();
	private List<Error> errors = new ArrayList<>();

	public ASTGenerator() {

	}

	public Environment getEnv() {
		return env;
	}

	public List<Error> getErrors() {
		return errors;
	}
	public int getNumOfErrors() {
		int r = 0;
		for(Error e : errors) {
			if(e.getErrSev() == ErrorSeverity.ERROR)
				++r;
		}
		return r;
	}
	public Program convertProgram(ProgContext ctx) throws IOException {
		List<Type> typeDeclerations = new ArrayList<>();
		List<Function> functionDeclerations = new ArrayList<>();
		List<Import> imports = new ArrayList<>();
		
		Program program = new Program(typeDeclerations, functionDeclerations,imports);
		
		Linker linker = new Linker(program,env);
		for(ImportDeclContext imp : ctx.imports().importDecl()) {
			String name;
			String transType;
			if(imp.importD() == null) {
				name = imp.importR().UNAME().getText();
				transType = "R";
			} else {
				name = imp.importD().UNAME().getText();
				transType = "D";
			}
			
			if(Environment.STD_MOD.containsKey(name)) {
				
				Import importt = convertImport(linker, name, transType);
				imports.add(importt);
				
			} else {
				String msg = "Import is not valid";
				Error err = new Error(imp.start.getLine(), imp.stop.getLine(), imp.start.getCharPositionInLine(), 
						imp.stop.getCharPositionInLine(), msg, ErrorSeverity.ERROR, new ArrayList<>());
				errors.add(err);
			}
			
		}
		
		for (DefContext def : ctx.def()) {
			if (def.typeDeclarations() != null) {
				Type t;
				try {
					if (def.typeDeclarations().dataTypeDecl() != null) {
						t = convertDataType(def.typeDeclarations().dataTypeDecl());
					} else {
						t = convertCoDataType(def.typeDeclarations().codataTypeDecl());
					}
					typeDeclerations.add(t);
				} catch (Exception e) {
					e.printStackTrace();
				}

			} else {
				Function f;
				try {
					if (def.functionDeclarations().functionDecl() != null) {
						f = convertOneExprFun(def.functionDeclarations().functionDecl());
					} else if (def.functionDeclarations().consumerFunctionDecl() != null) {
						f = convertConsumerFun(def.functionDeclarations().consumerFunctionDecl());
					} else {

						f = convertComatchFun(def.functionDeclarations().generatorFunctionDecl());
					}
					functionDeclerations.add(f);
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		}

		return program;
	}

	private Import convertImport(Linker linker, String name, String transType) throws IOException {
		DecompositionDiversityLexer lexer = new DecompositionDiversityLexer(CharStreams.fromFileName(""));
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		DecompositionDiversityParser parser = new DecompositionDiversityParser(tokens);
		
		ProgContext progCtx = parser.prog();
		
		ASTGenerator gen = new ASTGenerator();
		Program ast = gen.convertProgram(progCtx);
		
		BodiesGenerator bg = new BodiesGenerator(gen.getEnv(),progCtx);
        bg.generate();
        
        if(!Environment.STD_MOD.get(name).equals(transType)) {
        	ServerResponse<String> result = new ServerResponse<>();
        	ObjectMapper mapper = new ObjectMapper();
        	
        	ConnectionService connSer = new ConnectionServiceImpl();
			
        	JSONGenerator json = new JSONGenerator(ast);
    		JSONArray jj = json.getJson();
    		
    		Object prog = mapper.readValue(jj.toString(), Object.class);
    		JSONObject param = new JSONObject();

    		param.put(Constants.COQ_PROGRAM, prog);
    		param.put("typename", name);
        	
			if(transType.equals("R")) {
        		result = connSer.getResponse("destructorize",param);
        	} else {
        		result = connSer.getResponse("constructorize",param);
        	}
			
			JSONObject ppParams = new JSONObject();
			Object progToPrint = mapper.readValue(result.getData().toString(), Object.class);
			ppParams.put("program", progToPrint);
			Object config = mapper.readValue(Config.config.toJSON().toString(), Object.class);
			ppParams.put("config", config);
			
			CompilerService prettyPrint = new PrettyPrintProgramServiceImpl();
			ServerResponse<String> prettyProg = prettyPrint.perform(ppParams);
			JSONObject jsonRes = new JSONObject("{result:" + prettyProg.getData().toString() + "}");
			
			String toParse = jsonRes.getString("result");
			
			InputStream stream = new ByteArrayInputStream(toParse.getBytes(StandardCharsets.UTF_8));
			DecompositionDiversityLexer lexer2 = new DecompositionDiversityLexer(CharStreams.fromStream(stream, StandardCharsets.UTF_8));
			CommonTokenStream tokens2 = new CommonTokenStream(lexer2);
			
			DecompositionDiversityParser parser2 = new DecompositionDiversityParser(tokens2);
			
	        ProgContext progCtx2 = parser2.prog();
			
	        ASTGenerator gen2 = new ASTGenerator();
			Program ast2 = gen2.convertProgram(progCtx2);
			
			BodiesGenerator bg2 = new BodiesGenerator(gen.getEnv(),progCtx2);
	        bg2.generate();
	        
	       // addTranslateFunctions(ast2,gen2.getEnv());
	        
	        linker.link(ast2,gen2.getEnv());
        } else {
        	
        	//addTranslateFunctions(ast,gen.getEnv());
        	
        	linker.link(ast,gen.getEnv());
        }
        
        TRANSFORMATION trans = transType.equals("R")?TRANSFORMATION.Refunc:TRANSFORMATION.Defunc;
        Import imp = new Import(name, trans);
        
        env.getImports().add(imp);
		return imp;
	}

	private void addTranslateFunctions(Program ast, Environment env) {
		
		Token token = new NullToken();
		
		for(Type t : ast.getTypeDeclerations()) {
			String fName = "translate";
			MatchOrCoMatchFunction transFun;
			List<CaseOrCocase> body = new ArrayList<>();
			ArrayList<Variable> locals = new ArrayList<>();
			QualifiedName qn;
			ArrayList<Variable> arguments = new ArrayList<>();
			
			if(t instanceof DataType) {
				String typeName = t.getTypeName();
				
				fName += typeName;
				qn = new QualifiedName(typeName, fName);
				// true = DataType
				addBodies(t,body,true);
				
				transFun = new MatchFuction(token, token, typeName, qn, arguments, typeName, body, locals);
				
				ast.getFunctionDeclerations().add(transFun);
				env.getAllFuns().add(transFun);
				env.getTransFunMap().put(typeName, transFun);
			} else {
				
			}
		}
	}

	private void addBodies(Type t, List<CaseOrCocase> body, boolean isDataType) {
		Token token = new NullToken();
		
		for(ConstructorOrDestructor cd : t.getBody()) {
			Expression rightSide;
			List<Variable> vars = new ArrayList<>();
			generateVarLis(cd.getTypeNames(), vars);
			List<Expression> expList = new ArrayList<>();
			
			for(Variable v : vars) {
				expList.add(v);
			}
			
			if(isDataType) {
				rightSide = new ConstructorCall(token, token, t.getTypeName(), cd.getsName(), expList);
			} else {
				// receiver??
				rightSide = new DestructorCall(token, token, t.getTypeName(), cd.getsName(), expList, null);
			}
			
			CaseOrCocase cc = new CaseOrCocase(token, token, cd.getsName(), vars, rightSide);
			body.add(cc);
		}
	}

	private void generateVarLis(ArrayList<String> typeNames, List<Variable> vars) {
		Token token = new NullToken();
		
		for(String tn : typeNames) {
			String name = generateVarName(vars);
			
			Variable v = new Variable(token, token, tn, name);
			vars.add(v);
		}
	}

	private String generateVarName(List<Variable> arrayList) {
		Random random = new Random();
		
		List<String> vars = new ArrayList<>();
		
		for(Variable v:arrayList) {
			vars.add(v.getName());
		}
		
		// returns 1, 2, through 25
        int n = random.nextInt(26);
        char value;
        String p;
        
        do {
        	// Add 97 to move from integer to the range A to Z.
	        value = (char) (n + 97);
	        p = Character.toString(value);
        }while(vars.contains(p));
        
		return p;
	}
	private DataType convertDataType(DataTypeDeclContext dataTypeDecl) {
		String tName = dataTypeDecl.dataTypeDeclHeader().name.getText();

		int startLine = dataTypeDecl.dataTypeDeclHeader().name.getLine();
		int endLine = dataTypeDecl.dataTypeDeclHeader().name.getLine();
		int startCol = dataTypeDecl.dataTypeDeclHeader().name.getCharPositionInLine();
		int endCol = startCol+tName.length();

		if (env.lookUp(tName)) {
			String msg = "Type " + tName + " is already declared in the program and cannot be declared twice.";
			Error err = ErrorFactory.createError(startLine, endLine, startCol, endCol, msg);
			errors.add(err);
			throw new DuplicateNameException(msg);
		} else {
			List<ConstructorOrDestructor> body = new ArrayList<>();

			for (DecompositionDiversityParser.ConstructorDeclContext ctx : dataTypeDecl.dataTypeDeclBody().constructorDecl()) {
				Constructor constr = convertConstructor(ctx, tName);

				if (lookUp(body, constr.getsName())) {
					int startLineC = ctx.name.getLine();
					int endLineC = ctx.name.getLine();
					int startColC = ctx.name.getCharPositionInLine();
					int endColC = startColC + ctx.name.getText().length();
					String msg = "Constructor " + constr.getsName().getqName().getName()
							+ " is already declared for datatype " + tName + " and cannot be declared twice.";
					Error err = ErrorFactory.createError(startLineC, endLineC, startColC, endColC,msg);
					errors.add(err);
					throw new DuplicateNameException(msg);
				} else {
					body.add(constr);
				}
			}

			if (body.isEmpty()) {
				String msg = "No constructors are declared for datatype " + tName;
				Error warn = ErrorFactory.createWarning(startLine, endLine, startCol, endCol, msg);
				errors.add(warn);
			}

			Token start = dataTypeDecl.dataTypeDeclHeader().getStart();
			DataType t = new DataType(start, tName, body);
			env.getContext().put(tName, t);
			return t;
		}

	}

	private boolean lookUp(List<ConstructorOrDestructor> body, ScopedName sName) {
		String name = sName.getqName().getName();
		for (ConstructorOrDestructor cd : body) {
			if (cd.getsName().getqName().getName().equals(name))
				return true;
		}
		return false;
	}

	private Constructor convertConstructor(ConstructorDeclContext ctx, String tName) {
		String constName = ctx.name.getText();
		MODIFIER mod = constName.contains("_") ? MODIFIER.LOCAL : MODIFIER.GLOBAL;
		ScopedName scopedName = new ScopedName(mod, new QualifiedName(tName, constName));
		ArrayList<String> typeNames = new ArrayList<>();

		if (ctx.typeList() != null) {
			getTypeNames(typeNames, ctx.typeList());
		}
		Token start = ctx.getStart();
		Token stop = ctx.getStop();
		
		if(env.getConsAndNumOfTypes().containsKey(constName)) {
			int num = env.getConsAndNumOfTypes().get(constName)+1;
			env.getConsAndNumOfTypes().replace(constName, num);
		} else {
			env.getConsAndNumOfTypes().put(constName, 1);
		}
		return new Constructor(start, stop, scopedName, typeNames);
	}

	private void getTypeNames(ArrayList<String> typeNames, TypeListContext typeList) {

		if (typeList.typeList() == null) {
			typeNames.add(typeList.type.getText());
		} else {
			getTypeNames(typeNames, typeList.typeList());
			typeNames.add(typeList.type.getText());
		}
	}

	private CoDataType convertCoDataType(CodataTypeDeclContext codataTypeDecl) {
		String tName = codataTypeDecl.codataTypeDeclHeader().type.getText();

		int startLine = codataTypeDecl.codataTypeDeclHeader().type.getLine();
		int endLine = codataTypeDecl.codataTypeDeclHeader().type.getLine();
		int startCol = codataTypeDecl.codataTypeDeclHeader().type.getCharPositionInLine();
		int endCol = startCol+tName.length();

		if (env.lookUp(tName)) {
			String msg = "Type " + tName + " is already declared in the program and cannot be declared twice.";
			Error err = ErrorFactory.createError(startLine, endLine, startCol, endCol, msg);
			errors.add(err);

			throw new DuplicateNameException(msg);
		} else {
			List<ConstructorOrDestructor> body = new ArrayList<>();

			for (DestructorDeclContext destrDecl : codataTypeDecl.codataTypeDeclBody().destructorDecl()) {
				Destructor destr = convertDestructor(destrDecl, tName);

				if (lookUp(body, destr.getsName())) {
					int startLineC = destrDecl.name.getLine();
					int endLineC = destrDecl.name.getLine();
					int startColC = destrDecl.name.getCharPositionInLine();
					int endColC = startColC + destrDecl.name.getText().length();
					String msg = "Destructor " + destr.getsName().getqName().getName()
							+ " is already declared for codatatype " + tName + " and cannot be declared twice.";
					Error err = ErrorFactory.createError(startLineC, endLineC, startColC, endColC, msg);
					errors.add(err);
					throw new DuplicateNameException(msg);
				} else {
					body.add(destr);
				}

			}

			if (body.isEmpty()) {
				String msg = "No destructors are declared for codatatype " + tName;
				Error warn = ErrorFactory.createWarning(startLine, endLine, startCol, endCol, msg);

				errors.add(warn);
			}

			Token start = codataTypeDecl.codataTypeDeclHeader().getStart();
			CoDataType c = new CoDataType(start, tName, body);
			env.getContext().put(tName, c);
			return c;
		}

	}

	private Destructor convertDestructor(DestructorDeclContext destrDecl, String tName) {
		String destName = destrDecl.name.getText();
		MODIFIER mod = destName.contains("_") ? MODIFIER.LOCAL : MODIFIER.GLOBAL;
		ScopedName scopedName = new ScopedName(mod, new QualifiedName(tName, destName));

		ArrayList<String> typeNames = new ArrayList<>();

		if (destrDecl.typeList() != null)
			getTypeNames(typeNames, destrDecl.typeList());

		String returnType = destrDecl.returnType().getText();

		Token start = destrDecl.getStart();
		Token stop = destrDecl.getStop();
		
		if(env.getDesAndNumOfTypes().containsKey(destName)) {
			int num = env.getDesAndNumOfTypes().get(destName)+1;
			env.getDesAndNumOfTypes().replace(destName, num);
		} else {
			env.getDesAndNumOfTypes().put(destName, 1);
		}
		return new Destructor(start, stop, scopedName, typeNames, returnType);
	}

	private OneExprFunction convertOneExprFun(FunctionDeclContext functionDecl) {
		String funName = functionDecl.functionHeader().name.getText();

		Token start = functionDecl.getStart();
		Token stop = functionDecl.getStop();

		if (env.lookUpFunctionName(funName)) {
			int startLine = start.getLine();
			int endLine = functionDecl.functionHeader().getStop().getLine();
			int startCol = start.getCharPositionInLine();
			int endCol = functionDecl.functionHeader().getStop().getCharPositionInLine();
			String msg = "Function " + funName + " is already declared in the program and cannot be declared twice.";
			Error err = ErrorFactory.createError(startLine, endLine, startCol, endCol, msg);
			errors.add(err);

			throw new DuplicateNameException(msg);
		} else {
			ArrayList<Variable> arguments = new ArrayList<>();
			String returnType = functionDecl.functionHeader().returnType() == null ? funName + "$X$"
					: functionDecl.functionHeader().returnType().getText();

			ArrayList<Variable> localVars = new ArrayList<>();

			if (functionDecl.functionHeader().varDeclList() != null)
				getArguments(arguments, functionDecl.functionHeader().varDeclList(), localVars);

			HashMap<List<Variable>, String> argAndRet = new HashMap<>();

			argAndRet.put(arguments, returnType);

			env.getSignature().put(funName, argAndRet);

			Expression body = null;

			OneExprFunction fun = new OneExprFunction(start, stop, funName, arguments, returnType, body, localVars);

			if (returnType.contains("$X$"))
				env.getFunctionsWithTypeX().add(fun);

			env.getAllFuns().add(fun);

			return fun;
		}

	}

	private MatchFuction convertConsumerFun(ConsumerFunctionDeclContext consumerFunctionDecl) {
		String funName = consumerFunctionDecl.consumerFunHeader().name.getText();

		Token start = consumerFunctionDecl.getStart();
		Token stop = consumerFunctionDecl.consumerFunBody().getStop();

		if (env.lookUpFunctionName(funName)) {
			int startLine = start.getLine();
			int endLine = consumerFunctionDecl.consumerFunHeader().getStop().getLine();
			int startCol = start.getCharPositionInLine();
			int endCol = consumerFunctionDecl.consumerFunHeader().getStop().getCharPositionInLine();
			String msg = "Function " + funName + " is already declared in the program and cannot be declared twice.";
			Error err = ErrorFactory.createError(startLine, endLine, startCol, endCol, msg);
			errors.add(err);

			throw new DuplicateNameException(msg);
		} else {
			ArrayList<Variable> arguments = new ArrayList<>();
			String returnType = consumerFunctionDecl.consumerFunHeader().returnType() == null ? funName + "$X$"
					: consumerFunctionDecl.consumerFunHeader().returnType().getText();

			ArrayList<Variable> localVars = new ArrayList<>();

			String receiverType = funName + "$X$";

			if (consumerFunctionDecl.consumerFunHeader().receiverType() != null) {
				receiverType = consumerFunctionDecl.consumerFunHeader().receiverType().getText();
			} else {
				receiverType = "$X$" + funName;
			}

			if (consumerFunctionDecl.consumerFunHeader().argumentListCons().varDeclList() != null)
				getArguments(arguments, consumerFunctionDecl.consumerFunHeader().argumentListCons().varDeclList(),
						localVars);

			HashMap<List<Variable>, String> argAndRet = new HashMap<>();

			argAndRet.put(arguments, returnType);
			
			env.getSignature().put(funName, argAndRet);

			List<CaseOrCocase> body = new ArrayList<>();

			MatchFuction fun = new MatchFuction(start, stop, receiverType, new QualifiedName(receiverType, funName),
					arguments, returnType, body, localVars);

			if (receiverType.contains("$X$") || returnType.contains("$X$")) {
				env.getFunctionsWithTypeX().add(fun);
			}
			env.getAllFuns().add(fun);
			return fun;
		}

	}

	private Function convertComatchFun(GeneratorFunctionDeclContext generatorFunctionDecl) {
		String funName = generatorFunctionDecl.generatorFunHeader().name.getText();

		Token start = generatorFunctionDecl.getStart();
		Token stop = generatorFunctionDecl.generatorFunBody().getStop();

		if (env.lookUpFunctionName(funName)) {
			int startLine = start.getLine();
			int endLine = generatorFunctionDecl.generatorFunHeader().getStop().getLine();
			int startCol = start.getCharPositionInLine();
			int endCol = generatorFunctionDecl.generatorFunHeader().getStop().getCharPositionInLine();
			String msg = "Function " + funName + " is already declared in the program and cannot be declared twice.";
			Error err = ErrorFactory.createError(startLine, endLine, startCol, endCol, msg);
			errors.add(err);
			throw new DuplicateNameException(msg);
		} else {
			ArrayList<Variable> arguments = new ArrayList<>();
			String returnType = generatorFunctionDecl.generatorFunHeader().returnType() == null ? funName + "$X$"
					: generatorFunctionDecl.generatorFunHeader().returnType().getText();

			ArrayList<Variable> localVars = new ArrayList<>();

			if (generatorFunctionDecl.generatorFunHeader().argumentListGen().varDeclList() != null)
				getArguments(arguments, generatorFunctionDecl.generatorFunHeader().argumentListGen().varDeclList(),
						localVars);

			HashMap<List<Variable>, String> argAndRet = new HashMap<>();

			argAndRet.put(arguments, returnType);

			env.getSignature().put(funName, argAndRet);

			List<CaseOrCocase> body = new ArrayList<>();

			CoMatchFunction fun = new CoMatchFunction(start, stop, new QualifiedName(returnType, funName), arguments,
					returnType, body, localVars);

			if (returnType.contains("$X$")) {
				env.getFunctionsWithTypeX().add(fun);
			}
			env.getAllFuns().add(fun);
			return fun;
		}

	}

	private void getArguments(ArrayList<Variable> arguments, VarDeclListContext varDeclList,
			ArrayList<Variable> localVars) {
		if (varDeclList.varDeclList() == null) {
			Variable var = createVariable(varDeclList.varDecl());
			hasVar(localVars, var.getName(), varDeclList.varDecl().name.getLine(),
					varDeclList.varDecl().name.getCharPositionInLine(), 
					varDeclList.varDecl().name.getCharPositionInLine()+varDeclList.varDecl().name.getText().length());
			arguments.add(var);
			localVars.add(var);
		} else {
			getArguments(arguments, varDeclList.varDeclList(), localVars);
			Variable var = createVariable(varDeclList.varDecl());
			hasVar(localVars, var.getName(), varDeclList.varDecl().name.getLine(),
					varDeclList.varDecl().name.getCharPositionInLine(), 
					varDeclList.varDecl().name.getCharPositionInLine()+varDeclList.varDecl().name.getText().length());
			arguments.add(var);
			localVars.add(var);
		}
	}

	private void hasVar(ArrayList<Variable> localVars, String name, int line, int startCol, int endCol) {
		boolean has = false;
		for (Variable v : localVars) {
			if (v.getName().equals(name)) {
				has = true;
			}
		}
		if (has) {
			String msg = "Local variable "+name+ " is already declared and cannot be declared twice.";
			Error err = ErrorFactory.createError(line, line, startCol, endCol, msg);
			errors.add(err);
		}

	}

	private ArrayList<String> getLocalNames(ArrayList<Variable> localVars) {
		ArrayList<String> localNames = new ArrayList<>();
		for (Variable v : localVars) {
			localNames.add(v.getName());
		}
		return localNames;
	}

	private Variable createVariable(VarDeclContext varDecl) {
		Token start = varDecl.getStart();
		Token stop = varDecl.getStop();
		return new Variable(start, stop, varDecl.type.getText(), varDecl.name.getText());
	}

}
