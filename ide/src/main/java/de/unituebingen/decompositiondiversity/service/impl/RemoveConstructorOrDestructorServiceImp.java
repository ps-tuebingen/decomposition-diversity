/**
 * 
 */
package de.unituebingen.decompositiondiversity.service.impl;

import org.json.JSONArray;
import org.json.JSONObject;

import com.fasterxml.jackson.databind.ObjectMapper;

import de.unituebingen.decompositiondiversity.compiler.ast.Constructor;
import de.unituebingen.decompositiondiversity.compiler.ast.ConstructorOrDestructor;
import de.unituebingen.decompositiondiversity.compiler.ast.Destructor;
import de.unituebingen.decompositiondiversity.compiler.ast.Program;
import de.unituebingen.decompositiondiversity.compiler.ast.function.Function;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchOrCoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.OneExprFunction;
import de.unituebingen.decompositiondiversity.compiler.environment.Environment;
import de.unituebingen.decompositiondiversity.compiler.json.JSONGenerator;
import de.unituebingen.decompositiondiversity.helper.ASTWorker;
import de.unituebingen.decompositiondiversity.helper.Constants;
import de.unituebingen.decompositiondiversity.message.request.RemoveRequest;
import de.unituebingen.decompositiondiversity.message.request.Request;
import de.unituebingen.decompositiondiversity.message.response.ServerResponse;
import de.unituebingen.decompositiondiversity.service.CompilerService;
import de.unituebingen.decompositiondiversity.service.RefactoringService;

/**
 * @author Fayez Abu Alia
 *
 */
public class RemoveConstructorOrDestructorServiceImp implements RefactoringService {
	/** 
	 * Perform remove cons-/destructor from the program.
	 * 
	 *  @param params remove cons-/destructor request
	 *  @param env compilation environment for the program
	 *  @param program the JSON that has been compiled from source code
	 *  
	 *  @return  
	 */
	@Override
	public ServerResponse<String> perform(Request params, Environment env, Object program) {
		RemoveRequest req = (RemoveRequest) params;
		String name = req.getName();
		String typename = req.getTypename();
		ServerResponse<String> response = new ServerResponse<>();
		try {
			ConstructorOrDestructor cd = env.getConsOrDes(typename,name);
			
			CompilerService trans = null;
			CompilerService lastTrans = null;
			if(req.getType().equals("constructor")) {
				if(cd instanceof Destructor)
					return new ServerResponse<String>(Constants.ERROR, "Remove constructor is not avaliable on destructors");
				
				trans = new DestructorizeServiceImpl();
				lastTrans = new ConstructorizeServiceImpl();
			} else {
				if(cd instanceof Constructor)
					return new ServerResponse<String>(Constants.ERROR, "Remove destructor is not avaliable on constructors");
				
				trans = new ConstructorizeServiceImpl();
				lastTrans = new DestructorizeServiceImpl();
			}
//			String typename = cd.getsName().getqName().getTypeName();
			JSONObject pTrans = new JSONObject();
			pTrans.put(Constants.COQ_PROGRAM, program);
			pTrans.put(Constants.TYPENAME, typename);
			
			ServerResponse<String> transRes = trans.perform(pTrans);
			
			if(transRes.getStatus().equals(Constants.SUCCESS)) {
				
				try {
					ObjectMapper mapper = new ObjectMapper();
					String prog = mapper.readValue(transRes.getData().toString(), String.class);
					
					ASTWorker worker = new ASTWorker();
					Program ast = worker.generator(prog);
					
					Function toRemove = null;
					for(Function f: ast.getFunctionDeclerations()) {
						String funName;
						if(f instanceof OneExprFunction) {
							funName = ((OneExprFunction) f).getName();
						}else {
							funName = ((MatchOrCoMatchFunction) f).getqName().getName();
						}
						
						if(name.equals(funName)) {
							toRemove = f;
							break;
						}
					}
					
					if(toRemove != null) {
						System.out.println("TO REMOVE: " +  toRemove);
						ast.getFunctionDeclerations().remove(toRemove);
						
						JSONGenerator jsonGen = new JSONGenerator(ast);
						JSONArray jj = jsonGen.getJson();
						
						pTrans.remove(Constants.COQ_PROGRAM);
						pTrans.put(Constants.COQ_PROGRAM, jj);
						
						ServerResponse<String> lastTransRes = lastTrans.perform(pTrans);
						
						return lastTransRes;
						
						
					} else {
						response.setStatus(Constants.ERROR);
						response.setData("To remove is null.");
					}
				}catch (Exception e) {
					response.setStatus(Constants.ERROR);
					response.setData(e.getMessage());
					e.printStackTrace();
				}
			}else {
				return transRes;
			}
		} catch (Exception e) {
			response.setStatus(Constants.ERROR);
			response.setData(e.getMessage());
			e.printStackTrace();
		}
		
		return response;
	}

}
