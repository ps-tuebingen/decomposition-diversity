package de.unituebingen.decompositiondiversity.controller;


//import java.util.logging.Logger;

import org.springframework.stereotype.Controller;

import org.springframework.web.bind.annotation.ModelAttribute;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.servlet.ModelAndView;

import de.unituebingen.decompositiondiversity.model.Editor;

/**
 * 
 * @author Fayez Abu Alia
 *
 */
@Controller
public class IndexController {
//	private static final Logger logger = Logger.getLogger(IndexController.class.getName());

	@RequestMapping("/")
	public ModelAndView welcome(@ModelAttribute("editor") Editor editor) {
		
		ModelAndView model = new ModelAndView("index");

		return model;
	}
	
	@RequestMapping("/stepper")
	public ModelAndView stepper(@ModelAttribute("editor") Editor editor) {
		ModelAndView model = new ModelAndView("stepper");
		return model;
	}
}
