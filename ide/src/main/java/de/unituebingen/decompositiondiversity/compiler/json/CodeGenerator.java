package de.unituebingen.decompositiondiversity.compiler.json;

import org.json.JSONArray;
import org.json.JSONObject;

import de.unituebingen.decompositiondiversity.compiler.typechecker.SkeletonVisitor;
import de.unituebingen.decompositiondiversity.helper.Constants;

public class CodeGenerator {
	public CodeGenerator() {
		super();
	}

	/**
	 * @param tag String
	 * @param contents JSONArray
	 * @return JSONObject {"tag": tag, "contents":[]}
	 */
	public JSONObject createTagContentObj(String tag, JSONArray contents) {
		JSONObject d = new JSONObject();
		d.put(Constants.TAG,tag);
		d.put(Constants.CONTENTS, contents);
		return d;
	}
	
	/**
	 * @param tag String
	 * @param content int
	 * @return JSONObject {"tag": tag, "contents":int-Value}
	 */
	public JSONObject createTagContentObj(String tag, int content) {
		JSONObject d = new JSONObject();
		d.put(Constants.TAG,tag);
		d.put(Constants.CONTENTS, content);
		return d;
	}

}