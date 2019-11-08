/**
 * 
 */
package de.unituebingen.decompositiondiversity.service.impl;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import org.json.JSONObject;
import org.springframework.stereotype.Service;
import org.springframework.ui.Model;

import com.fasterxml.jackson.databind.ObjectMapper;

import de.unituebingen.decompositiondiversity.compiler.ast.Constructor;
import de.unituebingen.decompositiondiversity.compiler.ast.ConstructorOrDestructor;
import de.unituebingen.decompositiondiversity.compiler.ast.Import;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;
import de.unituebingen.decompositiondiversity.compiler.ast.function.Function;
import de.unituebingen.decompositiondiversity.compiler.environment.Environment;
import de.unituebingen.decompositiondiversity.compiler.parser.exception.NotDeclaredException;
import de.unituebingen.decompositiondiversity.compiler.parser.exception.DecompositionDiversityException;
import de.unituebingen.decompositiondiversity.helper.Constants;
import de.unituebingen.decompositiondiversity.message.request.GetBodyRequest;
import de.unituebingen.decompositiondiversity.message.request.Request;
import de.unituebingen.decompositiondiversity.message.response.CompilerResponse;
import de.unituebingen.decompositiondiversity.message.response.GetCasesResponse;
import de.unituebingen.decompositiondiversity.message.response.ServerResponse;
import de.unituebingen.decompositiondiversity.service.CompilerService;
import de.unituebingen.decompositiondiversity.service.HelperService;
import de.unituebingen.decompositiondiversity.service.LocalCompilerService;

/**
 * @author Fayez Abu Alia
 *
 */
@Service
public class GetBodyServiceImp implements HelperService {

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.service.HelperService#perform(de.unituebingen.decompositiondiversity.message.request.Request, java.lang.String)
	 */
	@Override
	public ServerResponse<GetCasesResponse> perform(Request req, String source, Model model) {
		ServerResponse<GetCasesResponse> res = new ServerResponse<>();

		GetBodyRequest params = (GetBodyRequest) req;
		String typename = params.getTypename();
		String type = params.getType();
                String signature = params.getSignature();

		GetCasesResponse data = new GetCasesResponse();

                String typeDeclHead = type.equals("constructor") ? "data " : "codata ";
		typeDeclHead += typename;
		typeDeclHead += " where";

		source = source.replace(typeDeclHead, typeDeclHead + "\n" + signature + " ");

		LocalCompilerService comp = new CompileServiceImpl();

		try {
			ObjectMapper mapper = new ObjectMapper();
			
			CompilerResponse cRes = comp.compile(source);
			if(cRes.getStatus().equals(Constants.ERROR)) {
                            String error_msg = "Signature is not correct: " + cRes.getResult().toString();
                            throw new DecompositionDiversityException(error_msg);
			}
			
			JSONObject param = new JSONObject();
			
			Object program = mapper.readValue(cRes.getResult(), Object.class);
			param.put(Constants.COQ_PROGRAM, program);
			param.put(Constants.TYPENAME, typename);

			
			CompilerService cs = type.equals("constructor")
                            ? new DestructorizeServiceImpl()
                            : new ConstructorizeServiceImpl();

			ServerResponse<String> trans = cs.perform(param);

			if (trans.getStatus().equals(Constants.SUCCESS)) {
				
				StringBuilder imports = new StringBuilder();
				for (Import im : cRes.getEnv().getImports()) {
					imports.append(im.toString() + "\n");
				}
				String prog = mapper.readValue(trans.getData().toString(), String.class);
				CompilerResponse rrr = comp.compile(imports.toString() + "\n" + prog);
				if (rrr.getNumOfErrors()>0)
					throw new NotDeclaredException(rrr.getStatus() + ": Compiler errors after first transformtion "
							+ rrr.getResult().toString());
				
				Environment env = rrr.getEnv();
				
				model.addAttribute(Constants.SESS_PROGRAM, rrr.getResult());
				model.addAttribute(Constants.SESS_SOURCE, imports.toString() + "\n" + prog);
				model.addAttribute(Constants.ENV, env);
				
				
				
				List<ConstructorOrDestructor> all = env.getType(typename).getBody();

				String sig = signature.substring(0, signature.indexOf("("));
				
				Function fun = env.getFunction(sig);

				String funBody = "";
				int startIdx = -1;
				int endIdx = -1;
				if (type.equals("constructor")) {
					startIdx = prog.indexOf("gfun " + sig);
					if (params.isParam()) {
						endIdx = getEndIDX("generator", prog, startIdx);
					} else {
						endIdx = prog.indexOf("=", startIdx) + 1;
					}
				} else {
					startIdx = prog.indexOf("cfun " + typename + ":" + sig);
					if (params.isParam()) {
						endIdx = getEndIDX("consumer", prog, startIdx);
					} else {
						endIdx = prog.indexOf("=", startIdx) + 1;
					}
				}
				funBody = prog.substring(startIdx, endIdx);

				if (!params.isParam()) {
					funBody += "\n";
					for (ConstructorOrDestructor cd : all) {
						String cName = cd.getsName().getqName().getName();
						String ccase = cd instanceof Constructor ? "\tcase " : "\tcocase ";
                                                ccase += cName;
                                                ccase += "(";
                                                ccase += getParams(cd.getTypeNames().size(), fun.getArguments());
                                                ccase += ") => \n";

						funBody += ccase;
					}

				}

				data.setBody(funBody);
				data.setConsAndDesMap(env.getConsAndDesMap());
				res.setStatus(Constants.SUCCESS);
				res.setData(data);
				return res;

			}
			res.setStatus(Constants.ERROR);
			data.setError((String) trans.getData());
			res.setData(data);

			

		} catch (IOException e) {
			e.printStackTrace();
			res.setStatus(Constants.ERROR);
			data.setError(e.getMessage());
			res.setData(data);
			
		}
		return res;
	}
	
	private int getEndIDX(String kw, String prog, int startIdx) {
		int endIdx = prog.indexOf(kw, startIdx + 1);

		if (endIdx == -1) {
			String[] kWords = { "consumer", "data", "codata", "function" };
			for (String k : kWords) {
				endIdx = prog.indexOf(k, startIdx);
				if (endIdx != -1)
					return endIdx;
			}
			if (endIdx == -1)
				endIdx = prog.length() - 1;
		}

		return endIdx;
	}

	private String getParams(int numOfParams, ArrayList<Variable> arrayList) {
		StringBuilder sb = new StringBuilder();
		Random random = new Random();

		List<String> vars = new ArrayList<>();

		for (Variable v : arrayList) {
			vars.add(v.getName());
		}

		for (int i = 0; i < numOfParams; ++i) {
			// returns 1, 2, through 25
			int n = random.nextInt(26);
			char value;
			String p;

			do {
				// Add 97 to move from integer to the range A to Z.
				value = (char) (n + 97);
				p = Character.toString(value);
			} while (vars.contains(p));

			vars.add(p);

			sb.append(value);
			if (i != numOfParams - 1)
				sb.append(",");
		}

		return sb.toString();
	}
}
