/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler.scope;

import org.json.JSONArray;

/**
 * @author Fayez Abu Alia
 *
 */
public class QualifiedName {
	
	private String typeName;
	private String name;
	
	public QualifiedName(String typeName, String name) {
		this.typeName = typeName;
		this.name = name;
	}
	
	public String getTypeName() {
		return typeName;
	}
	
	public void setTypeName(String typeName) {
		this.typeName = typeName;
	}
	
	public String getName() {
		return name;
	}
	
	public void setName(String name) {
		this.name = name;
	}
	
	public JSONArray toJSON() {
		String nn = name.contains("_")?name.substring(1):name;
		JSONArray json = new JSONArray();
		json.put(typeName);
		json.put(nn);
		
		return json;
	}
	
	@Override
	public String toString() {
		
		return typeName +" "+name;
	}

}
