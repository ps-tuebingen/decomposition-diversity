package de.unituebingen.decompositiondiversity.controller;

import java.io.IOException;
import java.util.ArrayList;

import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;
import org.springframework.ui.Model;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.RestController;
import org.springframework.web.bind.annotation.SessionAttribute;
import org.springframework.web.bind.annotation.SessionAttributes;

import com.fasterxml.jackson.databind.ObjectMapper;

import de.unituebingen.decompositiondiversity.compiler.ast.ConstructorOrDestructor;
import de.unituebingen.decompositiondiversity.compiler.ast.Import;
import de.unituebingen.decompositiondiversity.compiler.environment.Environment;
import de.unituebingen.decompositiondiversity.helper.Config;
import de.unituebingen.decompositiondiversity.helper.Constants;
import de.unituebingen.decompositiondiversity.helper.GetCases;
import de.unituebingen.decompositiondiversity.message.request.AddRequest;
import de.unituebingen.decompositiondiversity.message.request.EvalExprRequest;
import de.unituebingen.decompositiondiversity.message.request.ExtractFunctionRequest;
import de.unituebingen.decompositiondiversity.message.request.GetBodyRequest;
import de.unituebingen.decompositiondiversity.message.request.AutoCompleteRequest;
import de.unituebingen.decompositiondiversity.message.request.CompileRequest;
import de.unituebingen.decompositiondiversity.message.request.PrettyPrinterConfig;
import de.unituebingen.decompositiondiversity.message.request.RemoveRequest;
import de.unituebingen.decompositiondiversity.message.request.TransformationRequest;
import de.unituebingen.decompositiondiversity.message.request.GetCasesRequest;
import de.unituebingen.decompositiondiversity.message.request.GetConsOrDesListRequest;
import de.unituebingen.decompositiondiversity.message.request.InlineRequest;
import de.unituebingen.decompositiondiversity.message.response.CompileResponse;
import de.unituebingen.decompositiondiversity.message.response.CompilerResponse;
import de.unituebingen.decompositiondiversity.message.response.GetCasesResponse;
import de.unituebingen.decompositiondiversity.message.response.ServerResponse;
import de.unituebingen.decompositiondiversity.message.response.TransformationResponse;
import de.unituebingen.decompositiondiversity.model.Editor;
import de.unituebingen.decompositiondiversity.service.AutoCompleteService;
import de.unituebingen.decompositiondiversity.service.CompilerService;
import de.unituebingen.decompositiondiversity.service.HelperService;
import de.unituebingen.decompositiondiversity.service.RefactoringService;
import de.unituebingen.decompositiondiversity.service.impl.AddConstructorOrDestructorServiceImp;
import de.unituebingen.decompositiondiversity.service.impl.AddParameterServiceImp;
import de.unituebingen.decompositiondiversity.service.impl.AutoCompleteServiceImp;
import de.unituebingen.decompositiondiversity.service.impl.ConstructorizeServiceImpl;
import de.unituebingen.decompositiondiversity.service.impl.EvaluateExpressionServiceImpl;
import de.unituebingen.decompositiondiversity.service.impl.ExtractFunctionServiceImp;
import de.unituebingen.decompositiondiversity.service.impl.GetBodyServiceImp;
import de.unituebingen.decompositiondiversity.service.impl.InlineServiceImp;
import de.unituebingen.decompositiondiversity.service.impl.ParseProgamServiceImpl;
import de.unituebingen.decompositiondiversity.service.impl.PrettyPrintProgramServiceImpl;
import de.unituebingen.decompositiondiversity.service.impl.DestructorizeServiceImpl;
import de.unituebingen.decompositiondiversity.service.impl.RemoveConstructorOrDestructorServiceImp;


/**
 * 
 * @author Fayez Abu Alia
 *
 */
@RestController
@RequestMapping("/api")
@SessionAttributes({Constants.SESS_PROGRAM, Constants.SESS_SOURCE, Constants.ENV })
public class ServiceRestController {

	

	@RequestMapping(value = "/transformation", method = RequestMethod.POST)
	public ServerResponse<TransformationResponse> transform(@RequestBody TransformationRequest request,
			@SessionAttribute(Constants.SESS_SOURCE) String source, @SessionAttribute(Constants.SESS_PROGRAM) String program,
			@SessionAttribute(Constants.ENV) Environment env) throws IOException {

		ObjectMapper mapper = new ObjectMapper();

		Object prog = mapper.readValue(program, Object.class);
		
		String old = source;
		JSONObject param = new JSONObject();
		// param.put("program", Config.program);
//		param.put("program", editor.getProgram());
//		param.put("Coq_program", prog);
		param.put(Constants.COQ_PROGRAM, prog);
		param.put(Constants.TYPENAME, request.getTypename());

		CompilerService trans = null;

		if (request.getType().equals(Constants.REFUNC)) {
			trans = new DestructorizeServiceImpl();
		} else {
			trans = new ConstructorizeServiceImpl();
		}

		ServerResponse<String> result = trans.perform(param);
		
		ServerResponse<TransformationResponse> response = new ServerResponse<>();
		response.setStatus(result.getStatus());
		TransformationResponse data = new TransformationResponse();
		JSONObject json = new JSONObject("{result:" + result.getData().toString() + "}");
		if(result.getStatus().equals(Constants.SUCCESS)) {
			StringBuilder imports = new StringBuilder();
			for(Import im : env.getImports()) {
				imports.append(im.toString()+"\n");
			}
			data.setSource(imports.toString()+ "\n" + json.getString(Constants.RESULT));
			data.setOldSource(old);
		}else {
			data.setError(json.getString(Constants.RESULT));
		}
		response.setData(data);
		return response;
	}

	@RequestMapping(value = "/autocomplete", method = RequestMethod.POST)
	public ServerResponse<String> autocomplete(@RequestBody AutoCompleteRequest params, @SessionAttribute(Constants.ENV) Environment env) {
		AutoCompleteService ac = new AutoCompleteServiceImp();
		ServerResponse<String> response = ac.autoComplete(params,env);
		return response;
	}

	@RequestMapping(value = "/allData", method = RequestMethod.POST)
	public ServerResponse getData(@RequestBody Editor editor, @RequestParam("trans") String trans) throws IOException {
		String prog = editor.getValue();

		if (!prog.endsWith("\n"))
			prog += "\n";

		JSONObject param = new JSONObject();
		param.put("string", prog);

		ServerResponse response = new ServerResponse();

		JSONArray allData = null;
		if (trans.equals(Constants.REFUNC)) {
			allData = Config.datatypes;
		} else {
			allData = Config.codatatypes;
		}

		response.setStatus(Constants.SUCCESS);
		response.setData(allData.toString());

		return response;
	}

	@RequestMapping(value = "/parse", method = RequestMethod.POST)
	public ServerResponse parse(@RequestBody Editor editor) throws IOException {
		String prog = editor.getValue();

		if (!prog.endsWith("\n"))
			prog += "\n";

		JSONObject param = new JSONObject();
		param.put("string", prog);

		CompilerService parseProg = new ParseProgamServiceImpl();

		ServerResponse result = parseProg.perform(param);

		ServerResponse response = new ServerResponse();

		ObjectMapper mapper = new ObjectMapper();
		if (result.getStatus().equals("error")) {
			String errMsg = result.getData().toString();
			String[] errArray = errMsg.split(":");
			int len = errArray.length;
			JSONObject errJson = new JSONObject();
			errJson.put("line", errArray[0]);
			errJson.put("col", errArray[1]);
			String msg = errArray[2];

			for (int i = 3; i < len; ++i) {
				msg += errArray[i];
			}

			errJson.put("message", msg);

			editor.setResult(errJson.toString());
			response.setStatus("error");
		} else {
			JSONArray pProg = new JSONArray(result.getData().toString());

			Config.program = mapper.readValue(pProg.toString(), Object.class);

			editor.setResult(pProg.toString());
			response.setStatus(Constants.SUCCESS);
		}

		response.setData(editor);

		return response;
	}

	@RequestMapping(value = "/compile", method = RequestMethod.POST)
	public ServerResponse<CompileResponse> compile(@RequestBody CompileRequest request, 
			Model model) throws IOException {

		String prog = request.getSource();

		ServerResponse<CompileResponse> response = new ServerResponse<>();
		CompilerResponse res = Config.COMPILER.compile(prog);
		
		model.addAttribute(Constants.SESS_PROGRAM, res.getResult());
		model.addAttribute(Constants.SESS_SOURCE, prog);
		model.addAttribute(Constants.ENV, res.getEnv());
		
		CompileResponse data = new CompileResponse();
		response.setStatus(res.getStatus());
		
		if(res.getStatus().equals(Constants.SUCCESS) || res.getNumOfErrors()==0) {
			ArrayList<String> datanames = res.getEnv().getDataNames();
			ArrayList<String> codatanames = res.getEnv().getCoDataNames();
			data.setData(datanames);
			data.setCodata(codatanames);
			data.setConsAndDesMap(res.getEnv().getConsAndDesMap());
			data.setErrors(res.getWarnings());
		}
		
		if(res.getStatus().equals(Constants.ERROR)) {
			data.setErrors(res.getResult());
		}
		
		data.setNumOfErrors(res.getNumOfErrors());
		response.setData(data);
		return response;
	}

	@RequestMapping(value = "/exprEval", method = RequestMethod.POST)
	public ServerResponse<String> evalExp(@RequestBody EvalExprRequest cmd,@SessionAttribute(Constants.SESS_PROGRAM) String program) throws Exception {
		
		ObjectMapper mapper = new ObjectMapper();
		Object prog = mapper.readValue(program, Object.class);
		
		JSONObject param = new JSONObject();
//		String decExpr = UriUtils.decode(cmd.getExpr(), Charsets.UTF_8.toString());
//		String ex = cmd.getExpr().replace("_", "");
		param.put(Constants.COQ_PROGRAM, prog);
		param.put(Constants.COQ_EXPR, cmd.getExpr());
//		param.put("expr", ex);

		CompilerService eval = new EvaluateExpressionServiceImpl();
		ServerResponse<String> result = eval.perform(param);
		if (result.getStatus().equals(Constants.SUCCESS)) {
			JSONObject json = new JSONObject("{result:" + result.getData().toString() + "}");
			result.setData(json.getString(Constants.RESULT));
			System.out.println(result.getData().toString());

		}
		return result;

	}

	@RequestMapping(value = "/config", method = RequestMethod.POST)
	public ServerResponse getConfig() {

		ServerResponse res = new ServerResponse();

		JSONArray configs = new JSONArray();

		if (Config.config.isPrintQualifiedNames())
			configs.put("printQualifiedNames");

		if (Config.config.isPrintNat())
			configs.put("printNat");

		if (Config.config.isListOrderReversed())
			configs.put("listOrderReversed");

		if (Config.config.isPrintDeBruijn())
			configs.put("printDeBruijn");

		res.setStatus(Constants.SUCCESS);
		res.setData(configs.toString());

		return res;

	}

	@RequestMapping(value = "/setConfig", method = RequestMethod.POST)
	public ServerResponse<String> setConfig(@RequestBody PrettyPrinterConfig conf) {

		ServerResponse<String> res = new ServerResponse<>();

		Config.config.setPrintQualifiedNames(conf.isPrintQualifiedNames());
		Config.config.setPrintNat(conf.isPrintNat());
		Config.config.setListOrderReversed(conf.isListOrderReversed());
		Config.config.setPrintDeBruijn(conf.isPrintDeBruijn());

		res.setStatus(Constants.SUCCESS);
		res.setData("Pretty print config saved successfully");

		return res;

	}

	@RequestMapping(value = "/getCases", method = RequestMethod.POST)
	public ServerResponse<GetCasesResponse> getCases(@RequestBody GetCasesRequest params, @SessionAttribute(Constants.ENV) Environment env,
			@SessionAttribute(Constants.SESS_PROGRAM) String program, Model model) throws IOException {
		
		ObjectMapper mapper = new ObjectMapper();
		Object prog = mapper.readValue(program, Object.class);
		GetCases cc = new GetCases(env,prog);
		ServerResponse<GetCasesResponse> response;
		try {
			response = cc.getAllCases(params);
			
			model.addAttribute(Constants.SESS_PROGRAM, cc.getProgram().toString());
			model.addAttribute(Constants.SESS_SOURCE, cc.getSource());
			model.addAttribute(Constants.ENV, cc.getEnv());
			
		} catch (Exception e) {
			GetCasesResponse r = new GetCasesResponse();
			r.setError("Error occurs during program transformation.\n"+e.getMessage());
			response = new ServerResponse<GetCasesResponse>("error", r);
		}
		
		return response;
	}
	
	@RequestMapping(value = "/getBody", method = RequestMethod.POST)
	public ServerResponse<GetCasesResponse> getBody(@RequestBody GetBodyRequest params, @SessionAttribute(Constants.SESS_SOURCE) String source,
			 Model model) throws IOException {
		HelperService getBodyService = new GetBodyServiceImp();
		
		return getBodyService.perform(params, source, model);
	}
	
	@RequestMapping(value = "/getConsOrDesList", method = RequestMethod.POST)
	public ServerResponse<String> getConsOrDesList(@RequestBody GetConsOrDesListRequest params, @SessionAttribute(Constants.ENV) Environment env,
			 Model model) throws IOException {
		
		String tn = params.getTypename();
		JSONArray list;
		
		list = new JSONArray();
		for(ConstructorOrDestructor cd : env.getContext().get(tn).getBody()) {
			list.put(cd.getsName().getqName().getName());
		}
		
		ServerResponse<String> res = new ServerResponse<>(Constants.SUCCESS, list.toString());
		return res;
	}
	
	@RequestMapping(value = "/addConsOrDes", method = RequestMethod.POST)
	public ServerResponse<String> addConsOrDes(@RequestBody AddRequest params, @SessionAttribute(Constants.SESS_PROGRAM) String program,
			@SessionAttribute(Constants.SESS_SOURCE) String source,@SessionAttribute(Constants.ENV) Environment env) throws JSONException, IOException {
		
		params.setSource(source);
		ObjectMapper mapper = new ObjectMapper();
		Object prog = mapper.readValue(program, Object.class);
		
		RefactoringService add = new AddConstructorOrDestructorServiceImp();
		ServerResponse<String> result = add.perform(params,env,prog);
		if (result.getStatus().equals(Constants.SUCCESS)) {
			JSONObject json = new JSONObject("{result:" + result.getData().toString() + "}");
//			Response compile = Config.COMPILER.compile(json.getString("result"));
//			
//			if(compile.getStatus().equals("error")) {
//				return compile;
//			}
			StringBuilder imports = new StringBuilder();
			for(Import im : env.getImports()) {
				imports.append(im.toString()+"\n");
			}
			
			result.setData(imports.toString() + "\n"+json.getString(Constants.RESULT));
		}
		return result;
	}
	
	@RequestMapping(value = "/addParams", method = RequestMethod.POST)
	public ServerResponse<String> addParams(@RequestBody AddRequest params, @SessionAttribute(Constants.SESS_PROGRAM) String program,
			@SessionAttribute(Constants.SESS_SOURCE) String source,@SessionAttribute(Constants.ENV) Environment env) throws JSONException, IOException {
		
		params.setSource(source);
		ObjectMapper mapper = new ObjectMapper();
		Object prog = mapper.readValue(program, Object.class);
		
		RefactoringService add = new AddParameterServiceImp();
		ServerResponse<String> result = add.perform(params,env,prog);
		if (result.getStatus().equals(Constants.SUCCESS)) {
			JSONObject json = new JSONObject("{result:" + result.getData().toString() + "}");
//			Response compile = Config.COMPILER.compile(json.getString("result"));
//			
//			if(compile.getStatus().equals("error")) {
//				return compile;
//			}
			StringBuilder imports = new StringBuilder();
			for(Import im : env.getImports()) {
				imports.append(im.toString()+"\n");
			}
			
			result.setData(imports.toString() + "\n"+json.getString(Constants.RESULT));
		}
		return result;
	}
	
	@RequestMapping(value = "/extractFun", method = RequestMethod.POST)
	public ServerResponse<String> extractFunction(@RequestBody ExtractFunctionRequest request,  @SessionAttribute(Constants.SESS_PROGRAM) String program,
			@SessionAttribute(Constants.SESS_SOURCE) String source,@SessionAttribute(Constants.ENV) Environment env) throws JSONException, IOException {
		
		request.setSource(source);
		RefactoringService extract = new ExtractFunctionServiceImp();
		
		ServerResponse<String> response = extract.perform(request, env, program);
		if (response.getStatus().equals(Constants.SUCCESS)) {
			JSONObject json = new JSONObject("{result:" + response.getData().toString() + "}");
			StringBuilder imports = new StringBuilder();
			for(Import im : env.getImports()) {
				imports.append(im.toString()+"\n");
			}
			
			response.setData(imports.toString() + "\n"+json.getString(Constants.RESULT));

		}
		return response;
	}
	
	@RequestMapping(value = "/inline", method = RequestMethod.POST)
	public ServerResponse<String> inline(@RequestBody InlineRequest request,  @SessionAttribute(Constants.SESS_PROGRAM) String program,
			@SessionAttribute(Constants.SESS_SOURCE) String source,@SessionAttribute(Constants.ENV) Environment env) throws JSONException, IOException {
		
		request.setSource(source);
		RefactoringService in = new InlineServiceImp();
		
		ServerResponse<String> response = in.perform(request, env, program);
		if (response.getStatus().equals(Constants.SUCCESS)) {
			JSONObject json = new JSONObject("{result:" + response.getData().toString() + "}");
			StringBuilder imports = new StringBuilder();
			for(Import im : env.getImports()) {
				imports.append(im.toString()+"\n");
			}
			
			response.setData(imports.toString() + "\n"+json.getString(Constants.RESULT));
		}
		return response;
	}
	
	@RequestMapping(value = "/removeConsOrDes", method = RequestMethod.POST)
	public ServerResponse<String> removeConsOrDes(@RequestBody RemoveRequest request,  @SessionAttribute(Constants.SESS_PROGRAM) String program,
			@SessionAttribute(Constants.ENV) Environment env) throws JSONException, IOException {
		
		ObjectMapper mapper = new ObjectMapper();

		Object prog = mapper.readValue(program, Object.class);
		
		RefactoringService in = new RemoveConstructorOrDestructorServiceImp();
		
		ServerResponse<String> response = in.perform(request, env, prog);
		if (response.getStatus().equals(Constants.SUCCESS)) {
			JSONObject json = new JSONObject("{result:" + response.getData().toString() + "}");
			StringBuilder imports = new StringBuilder();
			for(Import im : env.getImports()) {
				imports.append(im.toString()+"\n");
			}
			
			response.setData(imports.toString() + "\n"+json.getString(Constants.RESULT));
		}
		return response;
	}
	
	@RequestMapping(value = "/format", method = RequestMethod.POST)
	public ServerResponse<String> format(@SessionAttribute(Constants.SESS_PROGRAM) String program) throws Exception {
		
		ObjectMapper mapper = new ObjectMapper();
		Object prog = mapper.readValue(program, Object.class);
		
		JSONObject param = new JSONObject();
		
		
		param.put(Constants.COQ_PROGRAM, prog);
		Object coqPr = mapper.readValue(program, Object.class);
		Config.config.setProgram(coqPr);
		Object config = mapper.readValue(Config.config.toJSON().toString(), Object.class);
		param.put(Constants.CONFIG, config);
		
		CompilerService prettyPrint = new PrettyPrintProgramServiceImpl();
		ServerResponse<String> prettyProg = prettyPrint.perform(param);
		if (prettyProg.getStatus().equals(Constants.SUCCESS)) {
			JSONObject json = new JSONObject("{result:" + prettyProg.getData().toString() + "}");
			prettyProg.setData(json.getString(Constants.RESULT));
		}
		return prettyProg;
		

	}
}
