package de.unituebingen.decompositiondiversity.message.request;
/**
 * 
 * @author Fayez Abu Alia
 *
 */

import org.json.JSONArray;
import org.json.JSONObject;

public class PrettyPrinterConfig {
	private Object program = new JSONArray();
	/**
	 * @return the program
	 */
	public Object getProgram() {
		return program;
	}

	/**
	 * @param program the program to set
	 */
	public void setProgram(Object program) {
		this.program = program;
	}
	private boolean printLocalFuns = false;
	private boolean printQualifiedNames = false;
	private boolean printNat = false;
	private boolean listOrderReversed = false;
	private boolean printDeBruijn = false;
	private int lvl = 0;
	
	/**
	 * @return the printLocalFuns
	 */
	public boolean isPrintLocalFuns() {
		return printLocalFuns;
	}

	/**
	 * @param printLocalFuns the printLocalFuns to set
	 */
	public void setPrintLocalFuns(boolean printLocalFuns) {
		this.printLocalFuns = printLocalFuns;
	}

	public boolean isPrintQualifiedNames() {
		return printQualifiedNames;
	}
	public void setPrintQualifiedNames(boolean printQualifiedNames) {
		this.printQualifiedNames = printQualifiedNames;
	}
	public boolean isPrintNat() {
		return printNat;
	}
	public void setPrintNat(boolean printNat) {
		this.printNat = printNat;
	}
	public boolean isListOrderReversed() {
		return listOrderReversed;
	}
	public void setListOrderReversed(boolean listOrderReversed) {
		this.listOrderReversed = listOrderReversed;
	}
	public boolean isPrintDeBruijn() {
		return printDeBruijn;
	}
	public void setPrintDeBruijn(boolean printDeBruijn) {
		this.printDeBruijn = printDeBruijn;
	}
	public int getLvl() {
		return lvl;
	}
	public void setLvl(int lvl) {
		this.lvl = lvl;
	}
	
	public JSONObject toJSON() {
		JSONObject configJSON = new JSONObject();
		configJSON.put("program", getProgram());
		configJSON.put("printLocalFuns", isPrintLocalFuns());
		configJSON.put("printQualifiedNames", isPrintQualifiedNames());
		configJSON.put("printNat", isPrintNat());
		configJSON.put("listOrderReversed", isListOrderReversed());
		configJSON.put("printDeBruijn", isPrintDeBruijn());
		configJSON.put("lvl", getLvl());
		
		return configJSON;
	}
}
