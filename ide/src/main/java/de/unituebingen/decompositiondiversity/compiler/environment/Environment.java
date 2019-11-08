/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler.environment;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.springframework.stereotype.Repository;
import org.springframework.stereotype.Service;

import de.unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase;
import de.unituebingen.decompositiondiversity.compiler.ast.Constructor;
import de.unituebingen.decompositiondiversity.compiler.ast.ConstructorOrDestructor;
import de.unituebingen.decompositiondiversity.compiler.ast.Destructor;
import de.unituebingen.decompositiondiversity.compiler.ast.Import;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Expression;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;
import de.unituebingen.decompositiondiversity.compiler.ast.function.CoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.Function;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchFuction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchOrCoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.OneExprFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.type.CoDataType;
import de.unituebingen.decompositiondiversity.compiler.ast.type.DataType;
import de.unituebingen.decompositiondiversity.compiler.ast.type.Type;
import de.unituebingen.decompositiondiversity.compiler.parser.exception.NotDeclaredException;
import de.unituebingen.decompositiondiversity.compiler.parser.exception.DecompositionDiversityException;
import de.unituebingen.decompositiondiversity.compiler.scope.QualifiedName;
import de.unituebingen.decompositiondiversity.compiler.scope.ScopedName;

/**
 * @author Fayez Abu Alia
 *
 */
public class Environment {
	public static final int GENFUNCTION = 2;
	public static final int CONSFUNCTION = 1;
	public static final int OEXFUNCTION = 0;
	public static final Map<String, String> STD_MOD = new HashMap<>();

	private final Map<String, Type> context = new HashMap<>();
	private final Map<String, Map<List<Variable>, String>> signature = new HashMap<>();
	// Constructorname with number of owners
	private final Map<String, Integer> consAndNumOfTypes = new HashMap<>();
	private final Map<String, Integer> desAndNumOfTypes = new HashMap<>();
	private final List<Function> functionsWithTypeX = new ArrayList<>();
	private final List<Function> allFuns = new ArrayList<>();
	private final List<Expression> exprWithTypeX = new ArrayList<>();
	private List<ScopedName> consDesWithTypeX = new ArrayList<>();
	private final List<Import> imports = new ArrayList<>();
	private final Map<String, MatchOrCoMatchFunction> transFunMap = new HashMap<>();
	private final List<Type> generatedTypes = new ArrayList<>();

	public Environment() {
		STD_MOD.put("Nat", "D");
		STD_MOD.put("Bool", "D");
	}

	public Map<String, Type> getContext() {
		return context;
	}

	public Map<String, Map<List<Variable>, String>> getSignature() {
		return signature;
	}

	public List<Function> getFunctionsWithTypeX() {
		return functionsWithTypeX;
	}

	public List<Function> getAllFuns() {
		return allFuns;
	}

	public List<Expression> getExprWithTypeX() {
		return exprWithTypeX;
	}

	public List<ScopedName> getConsDesWithTypeX() {
		return consDesWithTypeX;
	}

	/**
	 * @return the namesAndNumOfTypes
	 */
	public Map<String, Integer> getConsAndNumOfTypes() {
		return consAndNumOfTypes;
	}

	/**
	 * @return the dessAndNumOfTypes
	 */
	public Map<String, Integer> getDesAndNumOfTypes() {
		return desAndNumOfTypes;
	}

	/**
	 * @return the imports
	 */
	public List<Import> getImports() {
		return imports;
	}

	/**
	 * @return the transFunMap
	 */
	public Map<String, MatchOrCoMatchFunction> getTransFunMap() {
		return transFunMap;
	}

	public ArrayList<String> getDataNames() {
		ArrayList<String> data = new ArrayList<>();
		for (Type dt : context.values()) {
			if (dt instanceof DataType)
				data.add(dt.getTypeName());
		}
		return data;
	}

	public ArrayList<String> getCoDataNames() {
		ArrayList<String> codata = new ArrayList<>();
		for (Type cdt : context.values()) {
			if (cdt instanceof CoDataType)
				codata.add(cdt.getTypeName());
		}
		return codata;
	}

	public Map<String, String> getConsAndDesMap() {
		Map<String, String> map = new HashMap<>();
		for (Type t : context.values()) {
			for (ConstructorOrDestructor c : t.getBody()) {
				if(!map.containsKey(c.getsName().getqName().getName())) {
					String rBraket = (c instanceof Constructor) ? "[" : "(";
					String lBraket = (c instanceof Constructor) ? "]" : ")";
					String val = c.getsName().getqName().getName() + rBraket;
					int s = 1;
					for (String inf : c.getTypeNames()) {
						val += inf;
						if (s < c.getTypeNames().size())
							val += ",";
						++s;
					}
					val += lBraket;
					if(c instanceof Destructor)
						val += ":"+((Destructor) c).getReturnType();
					map.put(c.getsName().getqName().getName(), val);
				} else {
					map.remove(c.getsName().getqName().getName());
				}
				
			}
		}
		return map;
	}

	/**
	 * Check if context contains typeName
	 * 
	 * @param typeName
	 * @return
	 */
	public boolean lookUp(String typeName) {
		return context.containsKey(typeName);
	}

	public boolean lookUp(ScopedName sName) {
		String type = sName.getqName().getTypeName();
		String name = sName.getqName().getName();
		for (ConstructorOrDestructor cd : context.get(type).getBody()) {
			if (cd.getsName().getqName().getName().equals(name))
				return true;
		}
		return false;
	}

	public boolean lookUp(String name, List<Variable> vars, String returnType) {

		boolean hasFunName = signature.containsKey(name);
		return hasFunName;
	}

	public Type getType(String name) {
		return context.get(name);
	}

	public boolean isConstOrDesDeclared(String name, String typename) {
		ConstructorOrDestructor cd = getConsOrDes(typename, name);

		if (cd == null) {
			return false;
		} else {
			if (cd instanceof Constructor) {
				for (Function f : allFuns) {
					if (f instanceof MatchFuction) {
						for (CaseOrCocase cc : ((MatchFuction) f).getBody()) {
							if (cc.getName().getqName().getName().equals(name)
									&& cc.getName().getqName().getTypeName().equals(typename))
								return true;
						}
					}

				}
			} else {
				for (Function f : allFuns) {
					if (f instanceof CoMatchFunction) {
						for (CaseOrCocase cc : ((CoMatchFunction) f).getBody()) {
							if (cc.getName().getqName().getName().equals(name)
									&& cc.getName().getqName().getTypeName().equals(typename))
								return true;
						}
					}

				}
			}
		}
		return false;

	}

	public ScopedName lookUpConstrCall(String name) {
		if (consAndNumOfTypes.containsKey(name) && consAndNumOfTypes.get(name) == 1) {
			for (Type dt : context.values()) {
				if (dt instanceof DataType) {
					for (ConstructorOrDestructor c : ((DataType) dt).getBody()) {
						if (name.equals(c.getsName().getqName().getName())) {
							return c.getsName();
						}
					}
				}
			}
		}
		
		if(!consAndNumOfTypes.containsKey(name)) {
			throw new NotDeclaredException("Constructor "+name+" is not declared");
		}

		throw new DecompositionDiversityException(
				"constructor is not exist or there are more than one constructor with the same name");
	}

	public ScopedName lookUpConstrCall(String typename, String name) {
		for (Type dt : context.values()) {
			if (dt instanceof DataType) {
				if(dt.getTypeName().equals(typename)) {
					for (ConstructorOrDestructor c : ((DataType) dt).getBody()) {
						if (name.equals(c.getsName().getqName().getName())) {
							return c.getsName();
						}
					}
				}
			}
		}

		throw new DecompositionDiversityException("constructor is not exist");
	}

	public List<Variable> getArgs(String name) {
		for (Function f : allFuns) {
			String funName;
			if (f instanceof OneExprFunction) {
				funName = ((OneExprFunction) f).getName();
			} else {
				funName = ((MatchOrCoMatchFunction) f).getqName().getName();
			}
			if (name.equals(funName)) {
				return f.getArguments();
			}
		}
		return null;
	}

	public List<String> getArgsAsStringList(String name) {
		for (Function f : allFuns) {
			String funName;
			if (f instanceof OneExprFunction) {
				funName = ((OneExprFunction) f).getName();
			} else {
				funName = ((MatchOrCoMatchFunction) f).getqName().getName();
			}
			if (name.equals(funName)) {
				ArrayList<String> vars = new ArrayList<>();
				for (Variable v : f.getArguments()) {
					vars.add(v.getName());
				}
				return vars;
			}
		}
		throw new NotDeclaredException("function " + name + " is not declared.");
	}

	public Function getFunction(String name) {

		for (Function f : allFuns) {

			String funName;
			if (f instanceof OneExprFunction) {
				funName = ((OneExprFunction) f).getName();
			} else {
				funName = ((MatchOrCoMatchFunction) f).getqName().getName();
			}
			if (name.equals(funName)) {
				return f;
			}
		}
		System.out.println(allFuns.toString());
		throw new NotDeclaredException("Function " + name + " is not declared.");
	}

	public Destructor lookUpDestrCall(String name) {
		if (desAndNumOfTypes.containsKey(name) && desAndNumOfTypes.get(name) == 1) {
			for (Type t : context.values()) {
				if (t instanceof CoDataType) {
					CoDataType cdt = (CoDataType) t;
					for (ConstructorOrDestructor cd : cdt.getBody()) {
						if (name.equals(cd.getsName().getqName().getName())) {
							return (Destructor) cd;
						}
					}
				}
			}
		}

		throw new DecompositionDiversityException("Destructor does not exist or multiple destructor with the same name");
	}

	public Destructor lookUpDestrCall(String typeName, String name) {
		for (Type t : context.values()) {
			if (t instanceof CoDataType && t.getTypeName().equals(typeName)) {
				CoDataType cdt = (CoDataType) t;
				for (ConstructorOrDestructor cd : cdt.getBody()) {
					if (name.equals(cd.getsName().getqName().getName())) {
						return (Destructor) cd;
					}
				}
			}
		}

		throw new DecompositionDiversityException("Destructor does not exist");
	}

	public String lookUpFunType(String name) {
		for (Function f : allFuns) {
			String funName;
			if (f instanceof OneExprFunction) {
				funName = ((OneExprFunction) f).getName();
			} else {
				funName = ((MatchOrCoMatchFunction) f).getqName().getName();
			}
			if (name.equals(funName)) {
				return f.getReturnType();
			}
		}
		throw new NotDeclaredException("Function " + name + " is not declared.");
	}

	public boolean lookUpFunctionName(String name) {
		for (Function f : allFuns) {
			String funName;
			if (f instanceof OneExprFunction) {
				funName = ((OneExprFunction) f).getName();
			} else {
				funName = ((MatchOrCoMatchFunction) f).getqName().getName();
			}
			if (name.equals(funName)) {
				return true;
			}
		}
		return false;
	}

	public boolean lookUpVarName(String varName, Function fun) {
		for (Variable v : fun.getArguments()) {
			if (v.getName().equals(varName))
				return true;
		}
		return false;
	}

	public ConstructorOrDestructor getConsOrDes(String typeName, String constName) {
		for (Type t : context.values()) {
			for (ConstructorOrDestructor cd : t.getBody()) {
				if (cd.getsName().getqName().getTypeName().equals(typeName)
						&& cd.getsName().getqName().getName().equals(constName))
					return cd;
			}
		}
		throw new NotDeclaredException("Constructor or destructor " + constName + " is not declared.");
	}

	public ConstructorOrDestructor getConsOrDes(String typeName, String constName, boolean isCons) {
		String tn = typeName;
		if (typeName.contains("$X$")) {
			if (isCons) {
				if (consAndNumOfTypes.get(constName) == 1) {
					tn = getConsOrDesByName(constName);
					update(typeName, tn);
				} else {
					throw new DecompositionDiversityException("There are multiple constructors with same signature");
				}
			} else {
				if (desAndNumOfTypes.get(constName) == 1) {
					tn = getConsOrDesByName(constName);
					update(typeName, tn);
				} else {
					throw new DecompositionDiversityException("There are multiple destructors with same signature");
				}
			}

		}
		for (Type t : context.values()) {
			for (ConstructorOrDestructor cd : t.getBody()) {
				if (cd.getsName().getqName().getTypeName().equals(tn)
						&& cd.getsName().getqName().getName().equals(constName))
					return cd;
			}
		}
		throw new NotDeclaredException("Constructor or destructor " + constName + " is not declared.");
	}

	public ConstructorOrDestructor getConsOrDes(String typeName, String constName, boolean isCons, int numOfArgs) {
		String tn = typeName;
		if (typeName.contains("$X$")) {
			if (isCons) {
				if (consAndNumOfTypes.get(constName) == 1) {
					tn = getConsOrDesByName(constName);
					update(typeName, tn);
				} else {
					try {
						tn = getConsOrDesByNameAndNumOfArgs(constName, numOfArgs);
						update(typeName, tn);
					} catch (DecompositionDiversityException e) {
						throw e;
					}

				}
			} else {
				if (desAndNumOfTypes.get(constName) == 1) {
					tn = getConsOrDesByName(constName);
					update(typeName, tn);
				} else {
					try {
						tn = getConsOrDesByNameAndNumOfArgs(constName, numOfArgs);
						update(typeName, tn);
					} catch (DecompositionDiversityException e) {
						throw e;
					}

				}
			}

		}
		for (Type t : context.values()) {
			for (ConstructorOrDestructor cd : t.getBody()) {
				if (cd.getsName().getqName().getTypeName().equals(tn)
						&& cd.getsName().getqName().getName().equals(constName))
					return cd;
			}
		}
		throw new NotDeclaredException("Constructor or destructor " + constName + " is not declared.");
	}

	private String getConsOrDesByNameAndNumOfArgs(String constName, int numOfArgs) {
		boolean sameNum = false;
		String tn = null;
		for (Type t : context.values()) {
			for (ConstructorOrDestructor cd : t.getBody()) {
				if (cd.getsName().getqName().getName().equals(constName) && cd.getTypeNames().size() == numOfArgs) {
					if (!sameNum) {
						sameNum = true;
						tn = t.getTypeName();
					} else {
						throw new DecompositionDiversityException("There are multiple cons-/destructors with same signature");
					}
				}
			}
		}
		return tn;
	}

	private String getConsOrDesByName(String constName) {
		for (Type t : context.values()) {
			for (ConstructorOrDestructor cd : t.getBody()) {
				if (cd.getsName().getqName().getName().equals(constName))
					return t.getTypeName();
			}
		}
		return null;
	}

	/**
	 * substitute xType with type name tn.
	 * 
	 * @param xType type x
	 * @param tn    result of type x
	 */
	public void update(String xType, String tn) {
		ArrayList<ScopedName> namesToRemove = new ArrayList<>();
		for (ScopedName sn : consDesWithTypeX) {
			if (sn.getqName().getTypeName().equals(xType)) {
				sn.getqName().setTypeName(tn);

				if (!tn.contains("$X$"))
					namesToRemove.add(sn);
			}
		}

		consDesWithTypeX.removeAll(namesToRemove);

		ArrayList<Function> toRemove = new ArrayList<>();

		for (Function f : functionsWithTypeX) {
			if (f instanceof MatchFuction) {
				MatchFuction mf = (MatchFuction) f;
				if (mf.getReturnType().equals(xType)) {
					mf.setReturnType(tn);
				}
				if (mf.getReceiverType().equals(xType)) {
					mf.setReceiverType(tn);
					QualifiedName qName = mf.getqName();

					if (qName.getTypeName().equals(xType))
						qName.setTypeName(tn);
				}

				if (!tn.contains("$X$") && !mf.getReturnType().contains("$X$")
						&& !mf.getReceiverType().contains("$X$")) {
					toRemove.add(mf);
				}
			} else {
				if (f.getReturnType().equals(xType)) {
					f.setReturnType(tn);
					if (f instanceof CoMatchFunction) {
						QualifiedName qName = ((CoMatchFunction) f).getqName();
						if (qName.getTypeName().equals(xType)) {
							qName.setTypeName(tn);
						}
					}
					if (!tn.contains("$X$")) {
						toRemove.add(f);
					}
				}
			}

		}

		functionsWithTypeX.removeAll(toRemove);

		ArrayList<Expression> exprToRemove = new ArrayList<>();

		for (Expression e : exprWithTypeX) {
			TypeSetter ts = new TypeSetter(xType, tn);
			if (e.accept(ts)) {
				if (!tn.contains("$X$") && !e.accept(new HasTypeX()))
					exprToRemove.add(e);
			}

		}

		exprWithTypeX.removeAll(exprToRemove);
	}

	/**
	 * Get type name which contains the given constructors
	 * 
	 * @param allConstructors Map of constructor names and their variables
	 * @return type name or throw exception
	 */
	public String getTypeName(Map<QualifiedName, List<Variable>> allConstructors, boolean isDataType) {
		List<Type> maybe = new ArrayList<>();

		for (Type t : context.values()) {

//			if(allConstructors.size() != t.getBody().size())
//				continue;

			if ((isDataType && (t instanceof DataType)) || (!isDataType && (t instanceof CoDataType))) {
				boolean temp = true;
				for (QualifiedName qn : allConstructors.keySet()) {
					if (temp) {
						temp = hasConsOrDes(t, qn.getName(), allConstructors.get(qn).size());
					} else {
						break;
					}
				}
				if (temp)
					maybe.add(t);
			}
		}
		if (maybe.size() == 1)
			return maybe.get(0).getTypeName();

		throw new DecompositionDiversityException("There is no type");
	}

	private boolean hasConsOrDes(Type t, String name, int num) {
		for (ConstructorOrDestructor cd : t.getBody()) {
			if (cd.getsName().getqName().getName().equals(name) && cd.getTypeNames().size() == num)
				return true;
		}
		return false;
	}

	public String getTypeName(Map<QualifiedName, List<Variable>> allDestructors,
			Map<String, String> desWithReturnTypes) {
		List<Type> maybe = new ArrayList<>();

		for (Type t : context.values()) {

			if (t instanceof CoDataType) {
				boolean temp = true;
				for (QualifiedName qn : allDestructors.keySet()) {
					if (temp) {
						temp = hasConsOrDes(t, qn.getName(), allDestructors.get(qn).size());
					} else {
						break;
					}
				}
				if (temp)
					maybe.add(t);
			}
		}
		
		List<Type> toRemove = new ArrayList<>();
		
		for(Type t : maybe) {
			for(ConstructorOrDestructor cd : t.getBody()) {
				Destructor des = (Destructor) cd;
				String name = des.getsName().getqName().getName();
				String type = des.getReturnType();
				
				String typeToCom = desWithReturnTypes.get(name);
				
				if(!typeToCom.contains("$X$") && !typeToCom.equals(type)) {
					toRemove.add(t);
					break;
				}
			}
		}
		
		maybe.removeAll(toRemove);
		
		if (maybe.size() == 1)
			return maybe.get(0).getTypeName();

		throw new DecompositionDiversityException("There is no type");
	}

	/**
	 * @return the generatedTypes
	 */
	public List<Type> getGeneratedTypes() {
		return generatedTypes;
	}

	public Function getFunction(String name, int type) {
		for (Function f : allFuns) {
			
			if(type == OEXFUNCTION && !(f instanceof OneExprFunction)) {
				continue;
			} else if(type == CONSFUNCTION && !(f instanceof MatchFuction)) {
				continue;
			} else if(type==GENFUNCTION && !(f instanceof CoMatchFunction)) {
				continue;
			}
			String funName;
			if (f instanceof OneExprFunction) {
				funName = ((OneExprFunction) f).getName();
			} else {
				funName = ((MatchOrCoMatchFunction) f).getqName().getName();
			}
			if (name.equals(funName)) {
				return f;
			}
		}
		System.out.println(allFuns.toString());
		throw new NotDeclaredException("Function " + name + " is not declared.");
	}
	
}
