/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler.parser.error;

import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;
import org.antlr.v4.runtime.Token;
import org.json.JSONObject;

/**
 * @author Fayez Abu Alia
 *
 */
public class SyntaxError {
	 private final Recognizer<?, ?> recognizer;
	    private final Object offendingSymbol;
	    private final int line;
	    private final int charPositionInLine;
	    private final String message;
	    private final RecognitionException e;

	    SyntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol, int line, 
	    		int charPositionInLine, String msg, RecognitionException e){
	        this.recognizer = recognizer;
	        this.offendingSymbol = offendingSymbol;
	        this.line = line;
	        this.charPositionInLine = charPositionInLine;
	        this.message = msg;
	        this.e = e;
	    }

	    public Recognizer<?, ?> getRecognizer(){
	        return recognizer;
	    }

	    public Object getOffendingSymbol(){
	        return offendingSymbol;
	    }

	    public int getLine(){
	        return line;
	    }

	    public int getCharPositionInLine(){
	        return charPositionInLine;
	    }

	    public String getMessage(){
	        return message;
	    }

	    public RecognitionException getException() {
	        return e;
	    }
	    
	    public JSONObject toJSON() {
	    	JSONObject errJson = new JSONObject();
			errJson.put("line", line);
			errJson.put("stopLine", offendingSymbol==null?line:((Token)offendingSymbol).getLine());
			errJson.put("col", charPositionInLine);
			if(offendingSymbol == null) {
				errJson.put("stopCol", charPositionInLine);
			} else {
				errJson.put("stopCol", charPositionInLine+((Token)offendingSymbol).getText().length());
			}
			
			errJson.put("message", message);
			errJson.put("severity", "error");
			return errJson;
	    }
}
