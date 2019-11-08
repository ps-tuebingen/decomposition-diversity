/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler.linker;


import de.unituebingen.decompositiondiversity.compiler.ast.Program;
import de.unituebingen.decompositiondiversity.compiler.ast.function.Function;
import de.unituebingen.decompositiondiversity.compiler.ast.type.Type;
import de.unituebingen.decompositiondiversity.compiler.environment.Environment;

/**
 * @author Fayez Abu Alia
 *
 */
public class Linker {
	private Program astProgram;
	private Environment env;
	
	/**
	 * @param astProgram
	 * @param env 
	 */
	public Linker(Program astProgram, Environment env) {
		super();
		this.astProgram = astProgram;
		this.env = env;
	}


	public void link(Program astModule, Environment envMod) {
//		for(Type t : astModule.getTypeDeclerations()) {
//			astProgram.getTypeDeclerations().add(t);
//		}
//		
//		for(Function f : astModule.getFunctionDeclerations()) {
//			astProgram.getFunctionDeclerations().add(f);
//		}
		
		env.getContext().putAll(envMod.getContext());
		env.getAllFuns().addAll(envMod.getAllFuns());
		env.getSignature().putAll(envMod.getSignature());
		env.getTransFunMap().putAll(envMod.getTransFunMap());
	}
}
