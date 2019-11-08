/**
 * 
 */
package de.unituebingen.decompositiondiversity.helper;

import org.json.JSONArray;

import de.unituebingen.decompositiondiversity.compiler.environment.Environment;
import de.unituebingen.decompositiondiversity.message.request.PrettyPrinterConfig;
import de.unituebingen.decompositiondiversity.service.LocalCompilerService;
import de.unituebingen.decompositiondiversity.service.impl.CompileServiceImpl;

/**
 * @author Fayez Abu Alia
 *
 */
public class Config {
	/**
	 * the parsed program which written by the user
	 * in the editor.
	 */
	public static Object program = null;
	
	public static final LocalCompilerService COMPILER = new CompileServiceImpl();
	
	/**
	 * Pretty printer config.
	 */
	public static PrettyPrinterConfig config = new PrettyPrinterConfig();
	
	public static Environment env = null;
	
	
	
	public static JSONArray datatypes = new JSONArray();
	public static JSONArray codatatypes = new JSONArray();
}
