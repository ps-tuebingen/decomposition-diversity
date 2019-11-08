/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler.json;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.json.JSONArray;
import org.json.JSONObject;

import de.unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase;
import de.unituebingen.decompositiondiversity.compiler.ast.Constructor;
import de.unituebingen.decompositiondiversity.compiler.ast.ConstructorOrDestructor;
import de.unituebingen.decompositiondiversity.compiler.ast.Destructor;
import de.unituebingen.decompositiondiversity.compiler.ast.Program;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;
import de.unituebingen.decompositiondiversity.compiler.ast.function.CoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.Function;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchFuction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.OneExprFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.type.CoDataType;
import de.unituebingen.decompositiondiversity.compiler.ast.type.DataType;
import de.unituebingen.decompositiondiversity.compiler.ast.type.Type;
import de.unituebingen.decompositiondiversity.compiler.scope.MODIFIER;
import de.unituebingen.decompositiondiversity.compiler.scope.QualifiedName;
import de.unituebingen.decompositiondiversity.compiler.typechecker.SkeletonVisitor;
import de.unituebingen.decompositiondiversity.helper.Constants;

/**
 * @author Fayez Abu Alia
 *
 */
public class JSONGenerator extends CodeGenerator implements SkeletonVisitor {
	private JSONArray json = new JSONArray();
	private JSONArray skeleton = new JSONArray();
	private JSONArray functions = new JSONArray();
	private JSONArray mFunctions = new JSONArray();
	private JSONArray mLocalFunctions = new JSONArray();
	private JSONArray cmFunctions = new JSONArray();
	private JSONArray cmLocalFunctions = new JSONArray();
	private JSONArray dt = new JSONArray();
	private JSONArray cons = new JSONArray();
	private JSONArray cdt = new JSONArray();
	private JSONArray des = new JSONArray();
	private JSONArray fSig = new JSONArray();
	private JSONArray mfSig = new JSONArray();
	private JSONArray mfSigLocals = new JSONArray();
	private JSONArray cmfSig = new JSONArray();
	private JSONArray cmfSigLocals = new JSONArray();
	
	private final Map<QualifiedName, JSONObject> generatedJSONForConDes = new HashMap<>();
	private final Map<QualifiedName, Integer> conDesAndNumOfParam = new HashMap<>();
	
	/**
	 * @param prog
	 */
	public JSONGenerator(Program prog) {
		super();
		prog.accept(this);
	}

	public JSONArray getJson() {
		return json;
	}
	
	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.decompositiondiversity.ast.Program)
	 */
	@Override
	public void visit(Program program) {
		
		for(Type t: program.getTypeDeclerations()) {
			t.accept(this);
		}
		
		for(Function f : program.getFunctionDeclerations()) {
			f.accept(this);
		}
		skeleton.put(dt);
		skeleton.put(cons);
		skeleton.put(cdt);
		skeleton.put(des);
		skeleton.put(fSig);
		skeleton.put(mfSig);
		skeleton.put(mfSigLocals);
		skeleton.put(cmfSig);
		skeleton.put(cmfSigLocals);
		json.put(skeleton);
		json.put(functions);
		json.put(mFunctions);
		json.put(mLocalFunctions);
		json.put(cmFunctions);
		json.put(cmLocalFunctions);
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.decompositiondiversity.ast.type.DataType)
	 */
	@Override
	public void visit(DataType dataType) {
		String name = dataType.getTypeName();
		dt.put(name);
		for(ConstructorOrDestructor c : dataType.getBody()) {
			c.accept(this);
		}
		
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.decompositiondiversity.ast.type.CoDataType)
	 */
	@Override
	public void visit(CoDataType codataType) {
		String name = codataType.getTypeName();
		cdt.put(name);
		for(ConstructorOrDestructor c : codataType.getBody()) {
			c.accept(this);
		}

	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.decompositiondiversity.ast.Constructor)
	 */
	@Override
	public void visit(Constructor constr) {
		boolean global = constr.getsName().getModifier()==MODIFIER.GLOBAL; 
		String tag = global?Constants.COQ_GLOBAL:Constants.COQ_LOCAL;
		String fName = constr.getsName().getqName().getName();
		String name = global?fName:fName.substring(1);
		JSONArray contents = new JSONArray();
		contents.put(constr.getsName().getqName().getTypeName());
		contents.put(name);
		
		JSONObject con = createTagContentObj(tag, contents);
		
		generatedJSONForConDes.put(constr.getsName().getqName(), con);
		
		JSONArray args = new JSONArray();
		for(String t : constr.getTypeNames()) {
			args.put(t);
		}
		
		conDesAndNumOfParam.put(constr.getsName().getqName(), constr.getTypeNames().size());
		
		JSONArray jsonCon = new JSONArray();
		jsonCon.put(con);
		jsonCon.put(args);
		
		cons.put(jsonCon);
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.decompositiondiversity.ast.Destructor)
	 */
	@Override
	public void visit(Destructor destr) {
		boolean global = destr.getsName().getModifier()==MODIFIER.GLOBAL; 
		
		String tag = global?Constants.COQ_GLOBAL:Constants.COQ_LOCAL;
		String fName = destr.getsName().getqName().getName();
		String name = global?fName:fName.substring(1);
		
		JSONArray contents = new JSONArray();
		contents.put(destr.getsName().getqName().getTypeName());
		contents.put(name);
		JSONObject d = createTagContentObj(tag, contents);
		
		generatedJSONForConDes.put(destr.getsName().getqName(), d);
		
		JSONArray args = new JSONArray();
		for(String t : destr.getTypeNames()) {
			args.put(t);
		}
		
		conDesAndNumOfParam.put(destr.getsName().getqName(), destr.getTypeNames().size());
		
		JSONArray jsonDes = new JSONArray();
		jsonDes.put(d);
		jsonDes.put(args);
		
		JSONArray toAdd = new JSONArray();
		toAdd.put(jsonDes);
		toAdd.put(destr.getReturnType());
		
		des.put(toAdd);
		
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.decompositiondiversity.ast.function.OneExprFunction)
	 */
	@Override
	public void visit(OneExprFunction function) {
		JSONArray nameAndArgs = new JSONArray();
		nameAndArgs.put(function.getName());
		JSONArray args = new JSONArray();
		
		ArrayList<String> variables = new ArrayList<>();
		
		for(Variable v:function.getArguments()) {
			args.put(v.getType());
			variables.add(v.getName());
		}
		
		nameAndArgs.put(args);
		
		JSONArray withRet = new JSONArray();
		withRet.put(nameAndArgs);
		withRet.put(function.getReturnType());
		
		fSig.put(withRet);
		
		JSONArray body = new JSONArray();
		body.put(function.getName());
		
		ExpressionJSONGenerator gen = new ExpressionJSONGenerator(generatedJSONForConDes, variables);
		
		JSONObject ex = function.getBody().acceptJSONGen(gen);
		
		body.put(ex);
		functions.put(body);
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.decompositiondiversity.ast.function.MatchFuction)
	 */
	@Override
	public void visit(MatchFuction function) {
		JSONArray nameAndArgs = new JSONArray();
		JSONArray qName = new JSONArray();
		qName.put(function.getqName().getTypeName());
		qName.put(function.getqName().getName());
		nameAndArgs.put(qName);
		JSONArray args = new JSONArray();
		
		ArrayList<String> variables = new ArrayList<>();
		
		for(Variable v:function.getArguments()) {
			args.put(v.getType());
			variables.add(v.getName());
		}
		
		nameAndArgs.put(args);
		
		JSONArray withRet = new JSONArray();
		withRet.put(nameAndArgs);
		withRet.put(function.getReturnType());
		
		mfSig.put(withRet);
		
		JSONArray body = new JSONArray();
		String nn = function.getqName().getName();
		JSONArray qn = new JSONArray();
		qn.put(function.getqName().getTypeName());
		qn.put(nn);
		
//		body.put(function.getqName().toJSON());
		body.put(qn);
		
		JSONArray cc = convertCoCases(function.getBody(),variables);
		
		body.put(cc);
		mFunctions.put(body);
	}

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.decompositiondiversity.ast.function.CoMatchFunction)
	 */
	@Override
	public void visit(CoMatchFunction function) {
		JSONArray nameAndArgs = new JSONArray();
		JSONArray qName = new JSONArray();
		qName.put(function.getqName().getTypeName());
		qName.put(function.getqName().getName());
		nameAndArgs.put(qName);
		JSONArray args = new JSONArray();
		
		ArrayList<String> variables = new ArrayList<>();
		
		for(Variable v:function.getArguments()) {
			args.put(v.getType());
			variables.add(v.getName());
		}
		
		nameAndArgs.put(args);
		
		cmfSig.put(nameAndArgs);
		
		JSONArray body = new JSONArray();
		
		String nn = function.getqName().getName();
		JSONArray qn = new JSONArray();
		qn.put(function.getqName().getTypeName());
		qn.put(nn);
		
//		body.put(function.getqName().toJSON());
		body.put(qn);
		
		JSONArray cc = convertCoCases(function.getBody(), variables);
		
		body.put(cc);
		cmFunctions.put(body);
	}
	
	private JSONArray convertCoCases(List<CaseOrCocase> ccases, ArrayList<String> variables) {
		
		JSONArray body = new JSONArray();
		for(CaseOrCocase cc : ccases) {
			JSONArray ccJson = new JSONArray();
//			JSONObject des = generatedJSONForConDes.get(cc.getName().getqName());
			JSONObject des = getGeneratedJSON(cc.getName().getqName());
//			JSONArray desAndParam = new JSONArray();
//			desAndParam.put(des);
//			desAndParam.put(conDesAndNumOfParam.get(cc.getName().getqName()));
//			desAndParam.put(getNumOfParams(cc.getName().getqName()));
			ArrayList<String> lVars = new ArrayList<>();
			for(Variable v:cc.getParams()) {
				lVars.add(v.getName());
			}
			variables.addAll(0, lVars);
			
			
			ExpressionJSONGenerator exGen = new ExpressionJSONGenerator(generatedJSONForConDes, variables);
			JSONObject exp = cc.getExpr().acceptJSONGen(exGen);
//			ccJson.put(desAndParam);
			ccJson.put(des);
			ccJson.put(exp);
			body.put(ccJson);
			variables.removeAll(lVars);
		}
		return body;
	}

	private int getNumOfParams(QualifiedName qName) {
		for(QualifiedName qn : conDesAndNumOfParam.keySet()) {
			if(qName.getTypeName().equals(qn.getTypeName()) && qName.getName().equals(qn.getName()))
				return conDesAndNumOfParam.get(qn);
		}
		return -1;
	}

	private JSONObject getGeneratedJSON(QualifiedName qName) {
		for(QualifiedName qn : generatedJSONForConDes.keySet()) {
			if(qName.getTypeName().equals(qn.getTypeName()) && qName.getName().equals(qn.getName()))
				return generatedJSONForConDes.get(qn);
		}
		return null;
	}

}
