/**
 * 
 */
package de.unituebingen.decompositiondiversity.helper;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import org.json.JSONArray;
import org.json.JSONObject;

import com.fasterxml.jackson.databind.ObjectMapper;

import de.unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase;
import de.unituebingen.decompositiondiversity.compiler.ast.Constructor;
import de.unituebingen.decompositiondiversity.compiler.ast.ConstructorOrDestructor;
import de.unituebingen.decompositiondiversity.compiler.ast.Destructor;
import de.unituebingen.decompositiondiversity.compiler.ast.Import;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;
import de.unituebingen.decompositiondiversity.compiler.ast.function.CoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.Function;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchFuction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchOrCoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.environment.Environment;
import de.unituebingen.decompositiondiversity.compiler.parser.exception.NotDeclaredException;
import de.unituebingen.decompositiondiversity.message.request.GetCasesRequest;
import de.unituebingen.decompositiondiversity.message.response.CompilerResponse;
import de.unituebingen.decompositiondiversity.message.response.GetCasesResponse;
import de.unituebingen.decompositiondiversity.message.response.ServerResponse;
import de.unituebingen.decompositiondiversity.service.CompilerService;
import de.unituebingen.decompositiondiversity.service.LocalCompilerService;
import de.unituebingen.decompositiondiversity.service.impl.CompileServiceImpl;
import de.unituebingen.decompositiondiversity.service.impl.ConstructorizeServiceImpl;
import de.unituebingen.decompositiondiversity.service.impl.PrettyPrintProgramServiceImpl;
import de.unituebingen.decompositiondiversity.service.impl.DestructorizeServiceImpl;

/**
 * @author Fayez Abu Alia
 *
 */
public class GetCases {
	private Environment env;
	private Object program;
	private String source = "";

	/**
	 * @param env
	 */
	public GetCases(Environment env, Object program) {
		super();
		this.env = env;
		this.program = program;
	}

	public Environment getEnv() {
		return env;
	}

	public void setEnv(Environment env) {
		this.env = env;
	}

	public Object getProgram() {
		return program;
	}

	public void setProgram(Object program) {
		this.program = program;
	}

	public String getSource() {
		return source;
	}

	public void setSource(String source) {
		this.source = source;
	}

	public ServerResponse<GetCasesResponse> getAllCases(GetCasesRequest params) throws IOException {
		ServerResponse<GetCasesResponse> res = new ServerResponse<>();
		String type = params.getType();
		String typeName;

		Environment env2;
		GetCasesResponse data = new GetCasesResponse();
		try {
			ConstructorOrDestructor cd = env.getConsOrDes(params.getTypename(), params.getName());
			if (type == "") {
				type = (cd instanceof Constructor) ? "constructor" : "destructor";

			} else if (type.equals("constructor") && cd instanceof Destructor) {
				res.setStatus(Constants.ERROR);
				data.setError("Add " + type + " is not avaliable on " + params.getName() + ".");
				res.setData(data);
				return res;
			} else if (type.equals("destructor") && cd instanceof Constructor) {
				res.setStatus(Constants.ERROR);
				data.setError("Add " + type + " is not avaliable on " + params.getName() + ".");
				res.setData(data);
				return res;
			}

			typeName = cd.getsName().getqName().getTypeName();
		} catch (Exception e) {
			res.setStatus(Constants.ERROR);
			data.setError("Add " + type + " is not avaliable on " + params.getName() + ".");
			res.setData(data);
			return res;
		}

		if (!params.isParam() && env.isConstOrDesDeclared(params.getName(), typeName)) {
			res.setStatus(Constants.ERROR);
			data.setError("The " + type + " " + params.getName() + " is already exist.");
			res.setData(data);
			return res;
		}
		System.out.println(typeName);
		JSONObject param = new JSONObject();

		param.put(Constants.COQ_PROGRAM, program);
		param.put(Constants.TYPENAME, typeName);

		CompilerService cs;
		
		if (type.equals("constructor")) {
			cs = new DestructorizeServiceImpl();
		
		} else {
			cs = new ConstructorizeServiceImpl();
		}

		ServerResponse<String> trans = cs.perform(param);

		if (trans.getStatus().equals(Constants.SUCCESS)) {

			LocalCompilerService com = new CompileServiceImpl();
			try {
				ObjectMapper mapper = new ObjectMapper();
				StringBuilder imports = new StringBuilder();
				for (Import im : env.getImports()) {
					imports.append(im.toString() + "\n");
				}
				String prog = mapper.readValue(trans.getData().toString(), String.class);
				CompilerResponse rrr = com.compile(imports.toString() + "\n" + prog);
				if (rrr.getStatus().equals(Constants.ERROR))
					throw new NotDeclaredException(rrr.getStatus() + ": Compiler errors after first transformtion "
							+ rrr.getResult().toString());
				env2 = rrr.getEnv();

				setProgram(rrr.getResult());
				setEnv(env2);
				setSource(imports.toString() + "\n" + prog);

				List<ConstructorOrDestructor> all = env2.getType(typeName).getBody();

				String sig = params.getName();
				Function fun = env2.getFunction(sig);

				String funBody = "";
				int startIdx = -1;
				int endIdx = -1;
				if (type.equals("constructor")) {
					startIdx = prog.indexOf("generator function " + params.getName());
					if (params.isParam()) {
						endIdx = getEndIDX("generator", prog, startIdx);
					} else {
						endIdx = prog.indexOf("=", startIdx) + 1;
					}
				} else {
					startIdx = prog.indexOf("consumer function " + typeName + ":" + params.getName());
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
						String ccase = "";
						if (cd instanceof Constructor) {
							ccase = "\tcase " + cName;
							ccase += "[";
							ccase += getParams(cd.getTypeNames().size(), fun.getArguments());
							ccase += "] => \n";
						} else {
							ccase = "\tcocase " + cName;
							ccase += "(";
							ccase += getParams(cd.getTypeNames().size(), fun.getArguments());
							ccase += ") => \n";
						}
						funBody += ccase;
					}

				}

				data.setBody(funBody);
				data.setConsAndDesMap(env2.getConsAndDesMap());
				res.setStatus(Constants.SUCCESS);
				res.setData(data);

				return res;

			} catch (IOException e) {
				e.printStackTrace();
				throw e;
			}

		}
		data.setError((String) trans.getData());
		res.setData(data);

		return res;

	}

	private int getEndIDX(String kw, String prog, int startIdx) {
		int endIdx = prog.indexOf(kw, startIdx + 1);

		if (endIdx == -1) {
			String[] kWords = { "consumer","generator", "data", "codata", "function" };
			for (String k : kWords) {
				
				if(k.equals(kw))
					continue;
				
				endIdx = prog.indexOf(k, startIdx);
				if(k.equals("function") && endIdx<(startIdx+18)) {
					endIdx = -1;
					continue;
				}
				if (endIdx != -1)
					return endIdx;
			}
			if (endIdx == -1)
				endIdx = prog.length();
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
