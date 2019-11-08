/**
 * 
 */
package de.unituebingen.decompositiondiversity.compiler.typechecker;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.unituebingen.decompositiondiversity.compiler.ast.CaseOrCocase;
import de.unituebingen.decompositiondiversity.compiler.ast.Constructor;
import de.unituebingen.decompositiondiversity.compiler.ast.ConstructorOrDestructor;
import de.unituebingen.decompositiondiversity.compiler.ast.Destructor;
import de.unituebingen.decompositiondiversity.compiler.ast.Program;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;
import de.unituebingen.decompositiondiversity.compiler.ast.function.CoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.Function;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchFuction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchOrCoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.OneExprFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.type.CoDataType;
import de.unituebingen.decompositiondiversity.compiler.ast.type.DataType;
import de.unituebingen.decompositiondiversity.compiler.ast.type.Type;
import de.unituebingen.decompositiondiversity.compiler.environment.Environment;
import de.unituebingen.decompositiondiversity.compiler.parser.error.Error;
import de.unituebingen.decompositiondiversity.compiler.parser.error.ErrorFactory;
import de.unituebingen.decompositiondiversity.compiler.parser.error.Error.ErrorSeverity;
import de.unituebingen.decompositiondiversity.compiler.parser.exception.TypeException;
import de.unituebingen.decompositiondiversity.compiler.parser.exception.DecompositionDiversityException;
import de.unituebingen.decompositiondiversity.compiler.scope.QualifiedName;;

/**
 * @author Fayez Abu Alia
 *
 */
public class SkeletonChecker implements SkeletonVisitor {
	private static final String X = "$X$";
	private final Environment env;
	private final ArrayList<Error> typeErrors = new ArrayList<>();

	private final Map<Function, Boolean> visitState = new HashMap<>();
	private boolean validTypes = true;

	/**
	 * @param env
	 */
	public SkeletonChecker(Environment env) {
		super();
		this.env = env;
	}

	public ArrayList<Error> getTypeErrors() {
		return typeErrors;
	}

	public Environment getEnv() {
		return env;
	}
	public int getNumOfErrors() {
		int r = 0;
		for(Error e : typeErrors) {
			if(e.getErrSev() == ErrorSeverity.ERROR)
				++r;
		}
		return r;
	}
	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.
	 * decompositiondiversity.ast.Program)
	 */
	@Override
	public void visit(Program program) {
		for (Type t : program.getTypeDeclerations()) {
			t.accept(this);
		}

		for (Function f : program.getFunctionDeclerations()) {
			visitState.put(f, false);
		}
		if (validTypes) {
//			try {

			for (Function f : program.getFunctionDeclerations()) {
				if (f instanceof MatchFuction) {
					MatchFuction mf = (MatchFuction) f;
					if (!mf.getReceiverType().contains(X)) {
						if (!env.lookUp(mf.getReceiverType())) {
							int sLine = mf.getStart().getLine();
							int stLine = mf.getStop().getLine();
							int sCol = mf.getStart().getCharPositionInLine();
							int stCol = mf.getStop().getCharPositionInLine();

							String msg = "Receiver type " + mf.getReceiverType() + " is not declared.";

							Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
							typeErrors.add(err);
						} else if (env.getType(mf.getReceiverType()) instanceof CoDataType) {
							int sLine = mf.getStart().getLine();
							int stLine = mf.getStop().getLine();
							int sCol = mf.getStart().getCharPositionInLine();
							int stCol = mf.getStop().getCharPositionInLine();

							String msg = "data type " + mf.getReturnType() + " is not declared.";

							Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
							typeErrors.add(err);
						}
					}
					if (!mf.getReturnType().contains(X)) {
						if (!env.lookUp(mf.getReturnType())) {
							int sLine = mf.getStart().getLine();
							int stLine = mf.getStop().getLine();
							int sCol = mf.getStart().getCharPositionInLine();
							int stCol = mf.getStop().getCharPositionInLine();

							String msg = "Return type " + mf.getReturnType() + " is not declared.";

							Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
							typeErrors.add(err);
						} /*else if (env.getType(mf.getReturnType()) instanceof CoDataType) {
							int sLine = mf.getStart().getLine();
							int stLine = mf.getStop().getLine();
							int sCol = mf.getStart().getCharPositionInLine();
							int stCol = mf.getStop().getCharPositionInLine();

							String msg = "data type " + mf.getReturnType() + " is not declared.";

							Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
							typeErrors.add(err);
						}*/

					}
				}
				if (env.getFunctionsWithTypeX().contains(f))
					continue;
				boolean hasErr = false;
				if (!(f instanceof MatchFuction)) {
					if (!env.lookUp(f.getReturnType())) {
						int sLine = f.getStart().getLine();
						int stLine = f.getStop().getLine();
						int sCol = f.getStart().getCharPositionInLine();
						int stCol = f.getStop().getCharPositionInLine();

						String msg = "Return type " + f.getReturnType() + " is not declared.";

						Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
						typeErrors.add(err);
						hasErr = true;
					} else if (f instanceof CoMatchFunction && env.getType(f.getReturnType()) instanceof DataType) {
						int sLine = f.getStart().getLine();
						int stLine = f.getStop().getLine();
						int sCol = f.getStart().getCharPositionInLine();
						int stCol = f.getStop().getCharPositionInLine();

						String msg = "codata type " + f.getReturnType() + " is not declared.";

						Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
						typeErrors.add(err);
					}
				}
				if (!hasErr)
					f.accept(this);
				visitState.replace(f, true);
			}
			System.out.println("S Checker: ");
			for (int i = 0; i < env.getFunctionsWithTypeX().size(); ++i) {
				Function f = env.getFunctionsWithTypeX().get(i);
				System.out.println(f);
			}
			// First check all comatch functions and infer the missing
			// types. (see type rule)
			for (Function f : program.getFunctionDeclerations()) {
				if (f instanceof CoMatchFunction && env.getFunctionsWithTypeX().contains(f)) {
					f.accept(this);
					visitState.replace(f, true);
				}
			}

			for (Function f : program.getFunctionDeclerations()) {
				if (f instanceof MatchFuction && env.getFunctionsWithTypeX().contains(f)) {
					f.accept(this);
					if(visitState.get(f) == null) {
						visitState.replace(f, false);
					}else {
						visitState.replace(f, true);
					}
				}
			}

			for (Function f : program.getFunctionDeclerations()) {
				if (f instanceof OneExprFunction && env.getFunctionsWithTypeX().contains(f)) {
					f.accept(this);
					visitState.replace(f, true);
				}
			}

			for (Function f : program.getFunctionDeclerations()) {
				if (!visitState.get(f)) {
					f.accept(this);
					visitState.replace(f, true);
				}
			}
//			} catch (Exception e) {
//				e.printStackTrace();
//			}

		}

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.
	 * decompositiondiversity.ast.type.DataType)
	 */
	@Override
	public void visit(DataType dataType) {
		for (ConstructorOrDestructor cd : dataType.getBody()) {
			cd.accept(this);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.
	 * decompositiondiversity.ast.type.CoDataType)
	 */
	@Override
	public void visit(CoDataType codataType) {
		for (ConstructorOrDestructor cd : codataType.getBody()) {
			cd.accept(this);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.
	 * decompositiondiversity.ast.Constructor)
	 */
	@Override
	public void visit(Constructor constr) {
		for (String tn : constr.getTypeNames()) {
			if (!env.lookUp(tn)) {

				validTypes = false;

				int sLine = constr.getStart().getLine();
				int stLine = constr.getStop().getLine();
				int sCol = constr.getStart().getCharPositionInLine();
				int stCol = constr.getStop().getCharPositionInLine();

				String msg = "Type " + tn + " is not declared!";

				Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
				typeErrors.add(err);

			}
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.
	 * decompositiondiversity.ast.Destructor)
	 */
	@Override
	public void visit(Destructor destr) {
		if(!env.lookUp(destr.getReturnType())) {
			validTypes = false;

			int sLine = destr.getStart().getLine();
			int stLine = destr.getStop().getLine();
			int sCol = destr.getStart().getCharPositionInLine();
			int stCol = destr.getStop().getCharPositionInLine();

			String msg = "Type " + destr.getReturnType() + " is not declared!";

			Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
			typeErrors.add(err);
		}else {
			for (String tn : destr.getTypeNames()) {
				if (!env.lookUp(tn)) {

					validTypes = false;

					int sLine = destr.getStart().getLine();
					int stLine = destr.getStop().getLine();
					int sCol = destr.getStart().getCharPositionInLine();
					int stCol = destr.getStop().getCharPositionInLine();

					String msg = "Type " + tn + " is not declared!";

					Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
					typeErrors.add(err);

				}
			}
		}
		
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.
	 * decompositiondiversity.ast.function.OneExprFunction)
	 */
	@Override
	public void visit(OneExprFunction function) throws DecompositionDiversityException {

		for (Variable v : function.getArguments()) {
			if (!env.lookUp(v.getType())) {
				int sLine = v.getStart().getLine();
				int stLine = v.getStop().getLine();
				int sCol = v.getStart().getCharPositionInLine();
				int stCol = v.getStop().getCharPositionInLine();

				String msg = "Type " + v.getType() + " is not declared!";

				Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
				typeErrors.add(err);

				throw new TypeException(msg);
			}
		}
		
		int sLine = function.getStart().getLine();
		int stLine = function.getStop().getLine();
		int sCol = function.getStart().getCharPositionInLine();
		int stCol = function.getStop().getCharPositionInLine();
		
		String type = function.getReturnType();
		String expType = function.getBody().getType();
		
		if(!type.contains(X) && !expType.contains(X)) {
			if(!type.equals(expType)) {
				String msg = "The return type should be " + expType;

				Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
				typeErrors.add(err);

				throw new TypeException(msg);
			}
		} else {
			if(type.contains(X)) {
				env.update(type, expType);
			}
			if(expType.contains(X)) {
				env.update(expType, type);
			}
		}
		ExpressionChecker ie = new ExpressionChecker(env, typeErrors);
		Boolean bodyTypeCorr = function.getBody().accept(ie);

		if (bodyTypeCorr) {
			String inferredType = function.getBody().getType();
			if (type.contains(X) && !inferredType.contains(X)) {
				env.update(type, inferredType);
			} else if (!type.contains(X) && inferredType.contains(X)) {
				env.update(inferredType, type);
			} else if (type.contains(X) && inferredType.contains(X)) {
				// both types should be equal
				env.update(type, inferredType);
			} else {
				if (!type.equals(inferredType)) {

					String msg = "The return type should be " + inferredType;

					Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
					typeErrors.add(err);

					throw new TypeException(msg);
				}
			}
		}

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.
	 * decompositiondiversity.ast.function.MatchFuction)
	 */
	@Override
	public void visit(MatchFuction function) throws DecompositionDiversityException {
		for (Variable v : function.getArguments()) {
			if (!env.lookUp(v.getType())) {
				int sLine = v.getStart().getLine();
				int stLine = v.getStop().getLine();
				int sCol = v.getStart().getCharPositionInLine();
				int stCol = sCol + v.getStop().getCharPositionInLine() + v.getType().length();

				String msg = "Type " + v.getType() + " is not declared!";

				Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
				typeErrors.add(err);

				throw new TypeException(msg);

			}
		}
		int sLine = function.getStart().getLine();
		int stLine = function.getStop().getLine();
		int sCol = function.getStart().getCharPositionInLine();
		int stCol = function.getStop().getCharPositionInLine();

		// First get all constructors on the left side of cocases
		Map<QualifiedName, List<Variable>> allConstructors = getCostOrDest(function);
		// All constructors must belong to the same datatype
		if (!function.getBody().isEmpty()) {
			try {
				String typeName;
				if(function.getqName().getTypeName().contains(X)) {
					typeName = env.getTypeName(allConstructors, true);
					env.update(function.getqName().getTypeName(), typeName);
				} else {
					typeName = function.getqName().getTypeName();
				}
				// String typeName =
				// function.getBody().get(0).getName().getqName().getTypeName();
				boolean areTypesEqual = hasSameType(typeName, allConstructors, function);
				if (areTypesEqual) {

//					boolean correctTypes = checkArgumentTypes(allConstructors, function);
					try {
						checkArgumentTypes(allConstructors, function);

						String receiverType = function.getReceiverType();

						if (receiverType.contains(X)) {
							env.update(receiverType, typeName);
						} else {
							if (!receiverType.equals(typeName)) {

								String msg = "Type mismatch, the receiver type should be " + typeName;

								Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
								typeErrors.add(err);

								throw new TypeException(msg);
							}
						}

						Type dt = env.getType(typeName);
						dt.getAllFunctions().add(function);

						String inferredType = checkExpressionsMatchFun(function);

						if (function.getReturnType().contains(X) && !inferredType.contains(X)) {
							env.update(function.getReturnType(), inferredType);
						} else if (!function.getReturnType().contains(X) && inferredType.contains(X)) {
							env.update(inferredType, function.getReturnType());
						} else if (!function.getReturnType().contains(X) && !inferredType.contains(X)) {
							if (!inferredType.equals(function.getReturnType())) {
								String msg = "Type mismatch, the return type should be " + inferredType;

								Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
								typeErrors.add(err);

								throw new TypeException(msg);
							}
						} else {
							env.update(function.getReturnType(), inferredType);
						}

					} catch (DecompositionDiversityException e) {

						Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, e.getMessage());
						typeErrors.add(err);

					}
				}

			} catch (DecompositionDiversityException e) {
				visitState.replace(function, null);
//				String msg = "There is more than one type can be return type";
//
//				Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
//				typeErrors.add(err);

			}
		}

	}

	private String checkExpressionsMatchFun(MatchFuction function) {
		String type;
		if (!function.getReturnType().contains(X)) {
			type = function.getReturnType();
		} else {
			type = function.getBody().get(0).getExpr().getType();
		}

		ArrayList<String> usedCases = new ArrayList<>();

		for (CaseOrCocase cc : function.getBody()) {
			int sLine = cc.getStart().getLine();
			int stLine = cc.getStop().getLine();
			int sCol = cc.getStart().getCharPositionInLine();
			int stCol = cc.getStop().getCharPositionInLine();

			if (!usedCases.contains(cc.getName().getqName().getName())) {
				boolean hasErr = false;
				String exType = cc.getExpr().getType();
				if (type.contains(X) && !exType.contains(X)) {
					env.update(type, exType);
					type = exType;
				} else if (type.contains(X) && exType.contains(X)) {
					env.update(exType, type);
				} else if (!type.contains(X) && exType.contains(X)) {
					env.update(exType, type);
				} else if (!type.contains(X) && !exType.contains(X)) {
					if (!type.equals(exType)) {
						hasErr = true;
						String msg = "Type mismatch, type of expression should be " + type;

						Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
						typeErrors.add(err);
//						throw new TypeException(msg);
					}
				}
				if(!hasErr) {
					boolean corr = cc.getExpr().accept(new ExpressionChecker(env, typeErrors));
					if(corr && type.contains(X))
						type = cc.getExpr().getType();
				}
				
				usedCases.add(cc.getName().getqName().getName());

			} else {

				String msg = "This case is already used and can not be used twice.";

				Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
				typeErrors.add(err);
				throw new TypeException(msg);
			}

		}
		return type;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.unituebingen.decompositiondiversity.typechecker.SkeletonVisitor#visit(de.unituebingen.
	 * decompositiondiversity.ast.function.CoMatchFunction)
	 */
	@Override
	public void visit(CoMatchFunction function) throws DecompositionDiversityException {

		for (Variable v : function.getArguments()) {
			if (!env.lookUp(v.getType())) {
				int sLine = v.getStart().getLine();
				int stLine = v.getStop().getLine();
				int sCol = v.getStart().getCharPositionInLine();
				int stCol = v.getStop().getCharPositionInLine();

				String msg = "Type " + v.getType() + " is not declared!";

				Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
				typeErrors.add(err);

				throw new TypeException(msg);
			}
		}

		int sLine = function.getStart().getLine();
		int stLine = function.getStop().getLine();
		int sCol = function.getStart().getCharPositionInLine();
		int stCol = function.getStop().getCharPositionInLine();

		if (!function.getBody().isEmpty()) {
			// First get all destructor on the left side of cocases
			Map<QualifiedName, List<Variable>> allDestructors = getCostOrDest(function);
			Map<String, String> desWithReturnTypes = getDesWithRType(function);
			
			// All destructors must belong to the same codatatype
//			String typeName = function.getBody().get(0).getName().getqName().getTypeName();
			try {
				String typeName;
				if(function.getqName().getTypeName().contains(X)) {
					typeName = env.getTypeName(allDestructors, desWithReturnTypes);
					
					env.update(function.getqName().getTypeName(), typeName);
					
				} else {
					typeName = function.getqName().getTypeName();
				}
				
				
				boolean areTypesEqual = hasSameType(typeName, allDestructors, function);
				if (areTypesEqual && !typeName.contains(X)) {
					checkArgumentTypes(allDestructors, function);

					String funType = function.getReturnType();

					if (funType.contains(X)) {
						env.update(funType, typeName);
					} else {
						if (!funType.equals(typeName)) {
							String msg = "Type mismatch, the return type should be " + typeName;

							Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
							typeErrors.add(err);

							throw new TypeException(msg);
						}
					}

					Type cdt = env.getType(typeName);
					cdt.getAllFunctions().add(function);
					checkExpressionsCoMatchFun(function);
				}
			} catch (Exception e) {
				String msg = "There is more than one type can be return type";

				Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
				typeErrors.add(err);

			}

		}
	}

	private void checkExpressionsCoMatchFun(CoMatchFunction function) throws DecompositionDiversityException {

		ArrayList<String> usedCases = new ArrayList<>();
		for (CaseOrCocase cc : function.getBody()) {
			int sLine = cc.getStart().getLine();
			int stLine = cc.getStop().getLine();
			int sCol = cc.getStart().getCharPositionInLine();
			int stCol = cc.getStop().getCharPositionInLine();
			if (!usedCases.contains(cc.getName().getqName().getName())) {
				String tn = function.getReturnType();
				Destructor des;
				if (!tn.contains(X)) {
					des = env.lookUpDestrCall(tn, cc.getName().getqName().getName());
				} else {
					des = env.lookUpDestrCall(cc.getName().getqName().getName());
				}

				String rt = des.getReturnType();
				
				String exType = cc.getExpr().getType();
				if (exType.contains(X)) {
					env.update(exType, rt);
				} else {
					if(rt.contains(X)) {
						env.update(rt, exType);
					} else
					if (!exType.equals(rt)) {
						String msg = "Type mismatch, the type of expression should be " + rt;

						Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
						typeErrors.add(err);

						throw new TypeException(msg);
					}
				}
				
				cc.getExpr().accept(new ExpressionChecker(env, typeErrors));
				
				usedCases.add(cc.getName().getqName().getName());

			} else {
				String msg = "Cocase " + cc.getName().getqName().getName()
						+ " is already used and can not be used twice.";

				Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
				typeErrors.add(err);

				throw new TypeException(msg);
			}
		}
	}

	private boolean checkArgumentTypes(Map<QualifiedName, List<Variable>> all, MatchOrCoMatchFunction function) {
		boolean corr = true;
		for (QualifiedName qn : all.keySet()) {
			ConstructorOrDestructor cd = env.getConsOrDes(qn.getTypeName(), qn.getName());
			for (int i = 0; i < all.get(qn).size(); ++i) {
				String t = all.get(qn).get(i).getType();
				String shouldBe = cd.getTypeNames().get(i);
				if (t.contains(X)) {
					env.update(t, shouldBe);
				} else {
					if (!t.equals(shouldBe)) {
						corr = false;
						// TODO err MSG
						String msg = "Argument types are not correct";
						throw new DecompositionDiversityException(msg);
					}
				}

			}
		}
		return corr;
	}

	private boolean hasSameType(String typeName, Map<QualifiedName, List<Variable>> all,
			MatchOrCoMatchFunction function) {
		boolean same = true;
		for (QualifiedName qn : all.keySet()) {
			if (qn.getTypeName().contains(X)) {
				env.update(qn.getTypeName(), typeName);
			} else if (!typeName.equals(qn.getTypeName())) {
				same = false;
				String msg = "Type mismatch, the left side of function body shoud belong to " + typeName;
				int sLine = function.getStart().getLine();
				int stLine = function.getStop().getLine();
				int sCol = function.getStart().getCharPositionInLine();
				int stCol = function.getStop().getCharPositionInLine();

				Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
				typeErrors.add(err);
			}
		}
		return same;
	}

	private Map<QualifiedName, List<Variable>> getCostOrDest(MatchOrCoMatchFunction function) {
		Map<QualifiedName, List<Variable>> res = new HashMap<>();

		for (CaseOrCocase cc : function.getBody()) {
			res.put(cc.getName().getqName(), cc.getParams());
		}
		return res;
	}
	
	private Map<String, String> getDesWithRType(MatchOrCoMatchFunction function) {
		Map<String, String> res = new HashMap<>();

		for (CaseOrCocase cc : function.getBody()) {
			res.put(cc.getName().getqName().getName(), cc.getExpr().getType());
		}
		return res;
	}

}
