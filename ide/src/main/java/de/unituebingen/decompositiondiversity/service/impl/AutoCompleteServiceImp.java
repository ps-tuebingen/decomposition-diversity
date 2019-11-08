/**
 * 
 */
package de.unituebingen.decompositiondiversity.service.impl;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import org.json.JSONObject;
import org.springframework.stereotype.Service;

import de.unituebingen.decompositiondiversity.compiler.ast.ConstructorOrDestructor;
import de.unituebingen.decompositiondiversity.compiler.ast.type.CoDataType;
import de.unituebingen.decompositiondiversity.compiler.ast.type.DataType;
import de.unituebingen.decompositiondiversity.compiler.ast.type.Type;
import de.unituebingen.decompositiondiversity.compiler.environment.Environment;
import de.unituebingen.decompositiondiversity.message.request.AutoCompleteRequest;
import de.unituebingen.decompositiondiversity.message.response.ServerResponse;
import de.unituebingen.decompositiondiversity.service.AutoCompleteService;

/**
 * @author Fayez Abu Alia
 *
 */
@Service
public class AutoCompleteServiceImp implements AutoCompleteService {

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.service.AutoCompleteService#autoComplete(de.unituebingen.decompositiondiversity.model.Params)
	 */
	@Override
	public ServerResponse<String> autoComplete(AutoCompleteRequest params, Environment env) {
		ServerResponse<String> response = new ServerResponse<>();
		String type = params.getType();
		String name = params.getTypename();
		int start = (int) Math.ceil(params.getStart()/3.0);
		System.out.println(start);
		ArrayList<String> vars = params.getVars();
		
		StringBuilder sb = new StringBuilder();
		
//		try {
			
			Type t = env.getType(name);
			System.out.println(env.toString());
			int col = params.getCol();
			if(type.equals("data") && t instanceof DataType) {
				col += addBody(sb,t,vars,start,true);
			} else if(type.equals("codata") && t instanceof CoDataType) {
				col += addBody(sb,t,vars,start,false);
			} else {
				response.setStatus("error");
				response.setData("The given Type does not match with function!");
				return response;
			}
			response.setStatus("success");
			
			JSONObject res = new JSONObject();
			res.put("result", sb.toString());
			res.put("col", col);
			
			response.setData(res.toString());
			
//		}catch (Exception e) {
//			response.setStatus("error");
//			response.setData(e.getMessage());
//			e.printStackTrace();
//		}
		
		return response;
	}
	
	private int addBody(StringBuilder sb, Type t, List<String> vars, int start, boolean isDataType) {
		boolean first = false;
		int res = 0;
		for(ConstructorOrDestructor cd : t.getBody()) {
			String name = cd.getsName().getqName().getName();
			String params = getParams(cd.getTypeNames().size(),vars);
			sb.append("\n\t");
			
			for(int i=0;i<start;++i) {
				sb.append("\t");
			}
			
			if(isDataType) {
				sb.append("case "+name+"["+params+"] => ");
			}else {
				sb.append("cocase "+name+"("+params+") => ");
			}
			if(!first) {
				res += sb.length();
				first = true;
			}
		}
		return res;
	}

	private String getParams(int numOfParams, List<String> vars) {
		StringBuilder sb = new StringBuilder();
		Random random = new Random();
		for(int i=0;i<numOfParams;++i) {
			// returns 1, 2, through 25
	        int n = random.nextInt(26);
	        char value;
	        do {
	        	// Add 97 to move from integer to the range A to Z.
		        value = (char) (n + 97);
	        }while(vars.contains(Character.toString(value)));
	        
	        sb.append(value);
	        if(i!=numOfParams-1)
	        	sb.append(",");
		}
		
		return sb.toString();
	}
}
