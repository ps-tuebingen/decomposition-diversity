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
import de.unituebingen.decompositiondiversity.compiler.environment.Environment;
import de.unituebingen.decompositiondiversity.compiler.parser.exception.NotFoundException;
import de.unituebingen.decompositiondiversity.compiler.scope.MODIFIER;
import de.unituebingen.decompositiondiversity.compiler.scope.QualifiedName;
import de.unituebingen.decompositiondiversity.compiler.typechecker.ExpressionVisitor;
import de.unituebingen.decompositiondiversity.helper.Constants;

/**
 * @author Fayez Abu Alia
 *
 */
public class ExpressionJSONGenerator extends CodeGenerator implements ExpressionVisitor<JSONObject> {
	private ArrayList<String> variables;
	private final Map<QualifiedName, JSONObject> generatedJSONForConDes;
	// used in old version
	private final Map<QualifiedName, Integer> conDesAndNumOfParam = new HashMap<>();
	
	/**
	 * @param currentLvl
	 * @param lvlAndVars
	 * @param conDesAndNumOfParam 
	 */
	public ExpressionJSONGenerator(Map<QualifiedName, JSONObject> generatedJSONForConDes,ArrayList<String> variables) {
		super();
		this.generatedJSONForConDes = generatedJSONForConDes;
		this.variables = variables;
	}

	@Override
	public JSONObject visit(Variable variable) {
		String tag = Constants.VAR;
		
		int content = variables.indexOf(variable.getName());
		
		if(content == -1)
			throw new NotFoundException("Variable " + variable.getName() + " is not found");
		JSONObject v = new JSONObject();
		v.put(Constants.TAG, tag);
		v.put(Constants.CONTENTS, content);
		
		return v;
	}

	@Override
	public JSONObject visit(ConstructorCall constCall) {
		String tag = Constants.CONSCALL;
		JSONObject cons;
		if(Environment.STD_MOD.containsKey(constCall.getsName().getqName().getTypeName())) {
			boolean global = constCall.getsName().getModifier()==MODIFIER.GLOBAL; 
			String tag2 = global?Constants.COQ_GLOBAL:Constants.COQ_LOCAL;
			String fName = constCall.getsName().getqName().getName();
			String name = global?fName:fName.substring(1);
			JSONArray contents = new JSONArray();
			contents.put(constCall.getsName().getqName().getTypeName());
			contents.put(name);
			cons = createTagContentObj(tag2, contents);
			
		}else {
			cons = getCOrD(generatedJSONForConDes,constCall.getsName().getqName());
		}
		
		
		JSONArray contents = new JSONArray();
		contents.put(cons);
		
		JSONArray expressions = new JSONArray();
		for(Expression e: constCall.getExpressionList()) {
			JSONObject expJSON = e.acceptJSONGen(this);
			expressions.put(expJSON);
		}
		
		contents.put(expressions);
		
		JSONObject gJson = createTagContentObj(tag, contents);
		
		return gJson;
	}

	@Override
	public JSONObject visit(DestructorCall destrCall) {
		String tag = Constants.DESTRCALL;
		JSONObject des;
		if(Environment.STD_MOD.containsKey(destrCall.getsName().getqName().getTypeName())) {
			boolean global = destrCall.getsName().getModifier()==MODIFIER.GLOBAL; 
			
			String tag2 = global?Constants.COQ_GLOBAL:Constants.COQ_LOCAL;
			String fName = destrCall.getsName().getqName().getName();
			String name = global?fName:fName.substring(1);
			
			JSONArray contents = new JSONArray();
			contents.put(destrCall.getsName().getqName().getTypeName());
			contents.put(name);
			des = createTagContentObj(tag2, contents);
			
		} else {
			des = getCOrD(generatedJSONForConDes,destrCall.getsName().getqName());
		}
		
		
		JSONArray contents = new JSONArray();
		contents.put(des);
		
		JSONObject rec = destrCall.getReceiver().acceptJSONGen(this);
		contents.put(rec);
		
		JSONArray expressions = new JSONArray();
		for(Expression e: destrCall.getExpressionList()) {
			JSONObject expJSON = e.acceptJSONGen(this);
			expressions.put(expJSON);
		}
		
		contents.put(expressions);
		
		JSONObject gJson =createTagContentObj(tag, contents);
		
		return gJson;
	}

	@Override
	public JSONObject visit(FunctionCall funCall) {
		String tag = Constants.FUNCALL;
		JSONArray contents = new JSONArray();
		contents.put(funCall.getName());
		
		JSONArray expressions = new JSONArray();
		for(Expression e: funCall.getExpressions()) {
			JSONObject expJSON = e.acceptJSONGen(this);
			expressions.put(expJSON);
		}
		
		contents.put(expressions);
		
		JSONObject gJson = createTagContentObj(tag, contents);
		return gJson;
	}

	@Override
	public JSONObject visit(ComatchFunCall mFunCall) {
		String tag = Constants.GEN_FUNCALL;
		JSONArray contents = new JSONArray();
		
		String nn = mFunCall.getqName().getName();
		JSONArray qn = new JSONArray();
		qn.put(mFunCall.getqName().getTypeName());
		qn.put(nn);
		
		JSONObject sn = createTagContentObj(Constants.COQ_GLOBAL, qn);
//		contents.put(mFunCall.getqName().toJSON());
		contents.put(sn);
		JSONArray expressions = new JSONArray();
		for(Expression e: mFunCall.getExpressionList()) {
			JSONObject expJSON = e.acceptJSONGen(this);
			expressions.put(expJSON);
		}
		
		contents.put(expressions);
		
		JSONObject gJson = createTagContentObj(tag, contents);
		
		return gJson;
	}

	@Override
	public JSONObject visit(MatchFunCall cmFunCall) {
		String tag = Constants.CONS_FUNCALL;
		JSONArray contents = new JSONArray();
		
		String nn = cmFunCall.getqName().getName();
		JSONArray qn = new JSONArray();
		qn.put(cmFunCall.getqName().getTypeName());
		qn.put(nn);
		
		JSONObject sn = createTagContentObj(Constants.COQ_GLOBAL, qn);
//		contents.put(cmFunCall.getqName().toJSON());
		contents.put(sn);
		
		JSONObject rec = cmFunCall.getReceiver().acceptJSONGen(this);
		contents.put(rec);
		
		JSONArray expressions = new JSONArray();
		for(Expression e: cmFunCall.getExpressionList()) {
			JSONObject expJSON = e.acceptJSONGen(this);
			expressions.put(expJSON);
		}
		
		contents.put(expressions);
		
		JSONObject gJson = createTagContentObj(tag, contents);
		
		return gJson;
	}

	@Override
	public JSONObject visit(Match match) {
		
		String tag = Constants.MATCH;
		
		JSONArray contents = new JSONArray();
		contents.put(match.getqName().toJSON());
		
		JSONObject rec = match.getExpr().acceptJSONGen(this);
		contents.put(rec);
		
//		contents.put(match.getExpressionDeclList().size());
		
		JSONArray decl = new JSONArray();
		ArrayList<String> lVars = new ArrayList<>();
		for(ExprDecl exd : match.getExpressionDeclList()) {
			JSONObject var = exd.getRight().acceptJSONGen(this);
			JSONArray exdWithRet = new JSONArray();
			exdWithRet.put(var);
			exdWithRet.put(exd.getType());
			decl.put(exdWithRet);
			lVars.add(exd.getLeft().getName());
		}
		variables.addAll(0, lVars);
		
		contents.put(decl);
		JSONArray cc = convertCoCases(match.getBody());
		contents.put(cc);
		
		contents.put(match.getReturnType());
		
		JSONObject matchJson = createTagContentObj(tag, contents);
		// we use this method instead of removeAll because we want to remove
		// the new added variables and maybe the list has another variables
		// with the same name. (Just for match and comatch because of inline)
		removeAllFirstOccurrence(lVars);
//		variables.removeAll(lVars);
		return matchJson;
	}

	private void removeAllFirstOccurrence(ArrayList<String> lVars) {
		for(String v:lVars) {
			variables.remove(v);
		}
	}

	@Override
	public JSONObject visit(Comatch comatch) {
		
		String tag = Constants.COMATCH;
		
		JSONArray contents = new JSONArray();
		contents.put(comatch.getqName().toJSON());
//		contents.put(comatch.getExpressionDeclList().size());
		
		JSONArray decl = new JSONArray();
		ArrayList<String> lVars = new ArrayList<>();
		for(ExprDecl exd : comatch.getExpressionDeclList()) {
			JSONObject var = exd.getRight().acceptJSONGen(this);
			JSONArray exdWithRet = new JSONArray();
			exdWithRet.put(var);
			exdWithRet.put(exd.getType());
			decl.put(exdWithRet);
			lVars.add(exd.getLeft().getName());
		}
		variables.addAll(0, lVars);
		
		contents.put(decl);
		JSONArray cc = convertCoCases(comatch.getBody());
		contents.put(cc);
		
		JSONObject comatchJson = createTagContentObj(tag, contents);
		removeAllFirstOccurrence(lVars);
//		variables.removeAll(lVars);
		return comatchJson;
	}

	private JSONArray convertCoCases(List<CaseOrCocase> ccases) {
		
		JSONArray body = new JSONArray();
		
		for(CaseOrCocase cc : ccases) {
			JSONArray ccJson = new JSONArray();
			JSONObject des = getCOrD(generatedJSONForConDes,cc.getName().getqName());
			//JSONObject des = generatedJSONForConDes.get(cc.getName().getqName());
//			JSONArray desAndParam = new JSONArray();
//			desAndParam.put(des);
//			desAndParam.put(getNumOfParams(conDesAndNumOfParam,cc.getName().getqName()));
//			desAndParam.put(conDesAndNumOfParam.get(cc.getName().getqName()));
			ArrayList<String> lVars = new ArrayList<>();
			for(Variable v:cc.getParams()) {
				lVars.add(v.getName());
			}
			variables.addAll(0, lVars);
			
			JSONObject exp = cc.getExpr().acceptJSONGen(this);
//			ccJson.put(desAndParam);
			ccJson.put(des);
			ccJson.put(exp);
			body.put(ccJson);
			removeAllFirstOccurrence(lVars);
//			variables.removeAll(lVars);
		}
		return body;
	}

	private Integer getNumOfParams(Map<QualifiedName, Integer> conDesAndNumOfParam2, QualifiedName qName) {
		String tn = qName.getTypeName();
		String n = qName.getName();
		for(QualifiedName qn : conDesAndNumOfParam2.keySet()) {
			if(tn.equals(qn.getTypeName()) && n.equals(qn.getName()))
				return conDesAndNumOfParam2.get(qn);
		}
		throw new NotFoundException(qName +" is not found");
	}

	private JSONObject getCOrD(Map<QualifiedName, JSONObject> generatedJSONForConDes2, QualifiedName qName) {
		String tn = qName.getTypeName();
		String n = qName.getName();
		for(QualifiedName qn : generatedJSONForConDes2.keySet()) {
			if(tn.equals(qn.getTypeName()) && n.equals(qn.getName()))
				return generatedJSONForConDes2.get(qn);
		}
		throw new NotFoundException(qName +" is not found");
	}

	@Override
	public JSONObject visit(Let let) {
		
		String tag = Constants.LET;
		JSONArray contents = new JSONArray();
		JSONObject left = let.getLeft().getRight().acceptJSONGen(this);
		variables.add(0,let.getLeft().getLeft().getName());

		JSONObject right = let.getRight().acceptJSONGen(this);
		
		contents.put(left);
		contents.put(right);
		
		JSONObject letJson = createTagContentObj(tag, contents);
		
		return letJson;
	}

	@Override
	public JSONObject visit(CaseOrCocase caseOrCo) {
		return null;
	}

	@Override
	public JSONObject visit(ExprDecl exprD) {
		// TODO Auto-generated method stub
		return null;
	}

}
