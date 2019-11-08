package de.unituebingen.decompositiondiversity.service.impl;

import org.springframework.stereotype.Service;

/**
 * 
 * @author Fayez Abu Alia
 *
 */
@Service
public class PrettyPrintProgramServiceImpl extends PrettyPrintServiceImpl {

	public PrettyPrintProgramServiceImpl() {
		super.serviceName = "prettyPrintProgram";
	}

}
