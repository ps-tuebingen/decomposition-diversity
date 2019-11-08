/**
 * 
 */
package de.unituebingen.decompositiondiversity.service.impl;

import java.io.IOException;
import org.springframework.stereotype.Service;

import de.unituebingen.decompositiondiversity.compiler.ICompiler;
import de.unituebingen.decompositiondiversity.message.response.CompilerResponse;
import de.unituebingen.decompositiondiversity.service.LocalCompilerService;
import de.unituebingen.decompositiondiversity.compiler.impl.Compiler;;
/**
 * @author Fayez Abu Alia
 *
 */
@Service
public class CompileServiceImpl implements LocalCompilerService {

	/* (non-Javadoc)
	 * @see de.unituebingen.decompositiondiversity.service.LocalCompilerService#compile(java.lang.String)
	 */
	@Override
	public CompilerResponse compile(String prog) throws IOException {
		ICompiler compiler = new Compiler();
		return compiler.compile(prog);
	}

}
