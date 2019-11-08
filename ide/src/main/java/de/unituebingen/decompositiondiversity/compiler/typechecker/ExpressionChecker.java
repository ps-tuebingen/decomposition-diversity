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
import de.unituebingen.decompositiondiversity.compiler.ast.ExprDecl;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Comatch;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.ComatchFunCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.ConstructorCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.DestructorCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Expression;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.FunctionCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Let;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Match;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.MatchFunCall;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.MatchOrComatch;
import de.unituebingen.decompositiondiversity.compiler.ast.expression.Variable;
import de.unituebingen.decompositiondiversity.compiler.ast.function.CoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchFuction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.MatchOrCoMatchFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.function.OneExprFunction;
import de.unituebingen.decompositiondiversity.compiler.ast.type.DataType;
import de.unituebingen.decompositiondiversity.compiler.ast.type.Type;
import de.unituebingen.decompositiondiversity.compiler.environment.Environment;
import de.unituebingen.decompositiondiversity.compiler.parser.error.Error;
import de.unituebingen.decompositiondiversity.compiler.parser.error.ErrorFactory;
import de.unituebingen.decompositiondiversity.compiler.parser.error.Error.ErrorSeverity;
import de.unituebingen.decompositiondiversity.compiler.parser.exception.DecompositionDiversityException;
import de.unituebingen.decompositiondiversity.compiler.scope.QualifiedName;

/**
 * @author Fayez Abu Alia
 *
 */
public class ExpressionChecker implements ExpressionVisitor<Boolean> {
	private static final String X = "$X$";
	private final Environment env;
	private final ArrayList<Error> typeErrors;
	private boolean inMatchOrCoMatch = false;
	private List<String> varsMatchOrCoMatch = new ArrayList<>();

	/**
	 * @param env
	 */
	public ExpressionChecker(Environment env, ArrayList<Error> typeErrors) {
		super();
		this.env = env;
		this.typeErrors = typeErrors;
	}
	
	public int getNumOfErrors() {
		int r = 0;
		for(Error e : typeErrors) {
			if(e.getErrSev() == ErrorSeverity.ERROR)
				++r;
		}
		return r;
	}
	@Override
	public Boolean visit(Variable variable) {
		if (inMatchOrCoMatch && !varsMatchOrCoMatch.contains(variable.getName())) {
			int sLine = variable.getStart().getLine();
			int stLine = variable.getStop().getLine();
			int sCol = variable.getStart().getCharPositionInLine();
			int stCol = variable.getStop().getCharPositionInLine();

			String msg = variable.getName() + " should be declared in match/comatch header.";

			Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
			typeErrors.add(err);
			return false;
		}
		return true;
	}

	@Override
	public Boolean visit(ConstructorCall constCall) {
		boolean hasErr = false;
		try {
			String typeName = constCall.getsName().getqName().getTypeName();

			Constructor c = (Constructor) env.getConsOrDes(constCall.getsName().getqName().getTypeName(),
					constCall.getsName().getqName().getName(), true, constCall.getExpressionList().size());

			if (c.getTypeNames().size() != constCall.getExpressionList().size()) {
				int sLine = constCall.getStart().getLine();
				int stLine = constCall.getStop().getLine();
				int sCol = constCall.getStart().getCharPositionInLine();
				int stCol = constCall.getStop().getCharPositionInLine();

				String msg = "The Number of Arguments is not coorect";

				Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
				typeErrors.add(err);
				return hasErr;

			}
			for (int i = 0; i < c.getTypeNames().size(); ++i) {
				String tn = c.getTypeNames().get(i);
				Expression ex = constCall.getExpressionList().get(i);

				String exType = ex.getType();

				if (exType.contains(X)) {
					env.update(exType, tn);
				} else if (!tn.equals(exType)) {
					int sLine = ex.getStart().getLine();
					int stLine = ex.getStop().getLine();
					int sCol = ex.getStart().getCharPositionInLine();
					int stCol = ex.getStop().getCharPositionInLine();

					String msg = "Argument: " + ex.getInfo() + " should be " + tn;

					Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
					typeErrors.add(err);
					hasErr = true;
				}

				ex.accept(this);

			}

		} catch (Exception e) {
//			int sLine = constCall.getStart().getLine();
//			int stLine = constCall.getStop().getLine();
//			int sCol = constCall.getStart().getCharPositionInLine();
//			int stCol = constCall.getStop().getCharPositionInLine();
//
//			String msg = "Constructor " + constCall.getsName().getqName().getName() + " for type " + constCall.getType()
//					+ " is not declared";
//
//			Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
//			typeErrors.add(err);
			hasErr = true;

		}

		return !hasErr;
	}

	@Override
	public Boolean visit(DestructorCall destrCall) {
		boolean hasErr = false;

		int sLine = destrCall.getReceiver().getStart().getLine();
		int stLine = destrCall.getReceiver().getStop().getLine();
		int sCol = destrCall.getReceiver().getStart().getCharPositionInLine();
		int stCol = destrCall.getReceiver().getStop().getCharPositionInLine();
		String receiverType = destrCall.getReceiver().getType();
		try {
			Destructor d;
			if (receiverType.contains(X)) {
				d = (Destructor) env.getConsOrDes(destrCall.getsName().getqName().getTypeName(),
						destrCall.getsName().getqName().getName(), false, destrCall.getExpressionList().size());
			} else {
				d = (Destructor) env.getConsOrDes(receiverType, destrCall.getsName().getqName().getName());
			}

			String typename = destrCall.getsName().getqName().getTypeName();

			if (d.getTypeNames().size() != destrCall.getExpressionList().size()) {

				String msg = "The Number of Arguments is not correct";

				Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
				typeErrors.add(err);
				return hasErr;
			}
			if (receiverType.contains(X)) {
				env.update(receiverType, typename);
			} else {
				if (typename.contains(X)) {
					env.update(typename, receiverType);
				} else {
					if (!typename.equals(receiverType)) {

						String msg = "Receiver " + destrCall.getReceiver().getInfo() + " should be " + typename;

						Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
						typeErrors.add(err);

						return hasErr;
					}
				}
			}
			destrCall.getReceiver().accept(this);
			for (int i = 0; i < d.getTypeNames().size(); ++i) {
				String tn = d.getTypeNames().get(i);
				Expression ex = destrCall.getExpressionList().get(i);
				boolean exTest = ex.accept(this);
				String exType = ex.getType();
				if (exTest) {
					if (exType.contains(X)) {
						env.update(exType, tn);
					} else if (!tn.equals(exType)) {

						String msg = "Argument: " + ex.getInfo() + " should be " + tn;

						Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
						typeErrors.add(err);
						hasErr = true;
					}

				}
			}

			String returnType = destrCall.getType();
			String desRT = d.getReturnType();
			if (returnType.contains(X)) {
				env.update(returnType, desRT);
			}
		} catch (DecompositionDiversityException e) {
			String msg = e.getMessage();

			Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
			typeErrors.add(err);
			hasErr = true;
		}

		return !hasErr;
	}

	@Override
	public Boolean visit(FunctionCall funCall) {
		OneExprFunction f = (OneExprFunction) env.getFunction(funCall.getName());
		boolean hasErr = hasErrors(f.getArguments(), funCall.getExpressions(), f.getStart().getLine(),
				f.getStart().getLine(), f.getStart().getCharPositionInLine(), f.getStop().getCharPositionInLine());

		return !hasErr;
	}

	@Override
	public Boolean visit(ComatchFunCall mFunCall) {
		CoMatchFunction f = (CoMatchFunction) env.getFunction(mFunCall.getqName().getName());
		boolean hasErr = hasErrors(f.getArguments(), mFunCall.getExpressionList(), mFunCall.getStart().getLine(),
				mFunCall.getStart().getLine(), mFunCall.getStart().getCharPositionInLine(),
				mFunCall.getStop().getCharPositionInLine());

		return !hasErr;
	}

	private boolean hasErrors(ArrayList<Variable> arguments, List<Expression> expressionList, int sLine, int stLine,
			int sCol, int stCol) {
		boolean hasErr = false;
		for (int i = 0; i < arguments.size(); ++i) {
			String type = arguments.get(i).getType();
			//TODO: add try/catch to catch error
			try {
				Expression ex = expressionList.get(i);
//				ex.accept(this);
				String exType = ex.getType();
	
				if (exType.contains(X)) {
					env.update(exType, type);
	//					ex.accept(this);
				} else if (!type.equals(exType)) {
	
					String msg = "Argument: " + ex.getInfo() + " should be " + type;
	
					Error err = ErrorFactory.createError(ex.getStart().getLine(), ex.getStart().getLine(),
							ex.getStart().getCharPositionInLine(), ex.getStop().getCharPositionInLine(), msg);
					typeErrors.add(err);
					hasErr = true;
				}
				if (!hasErr)
					ex.accept(this);
			} catch (Exception e) {
				e.printStackTrace();
			}
			
		}
		return hasErr;
	}

	@Override
	public Boolean visit(MatchFunCall cmFunCall) {
		MatchFuction f = (MatchFuction) env.getFunction(cmFunCall.getqName().getName());
		Expression receiver = cmFunCall.getReceiver();
		// String inferredType = receiver.accept(this);
		receiver.accept(this);
		String recTypeFun = f.getReceiverType();
		String recType = receiver.getType();

		boolean validRecT = true;
		if (!recTypeFun.contains(X) && !recType.contains(X)) {
			if (!recTypeFun.equals(recType)) {
				String msg = "Receiver type should be " + recTypeFun + "";

				Error err = ErrorFactory.createError(receiver.getStart().getLine(), receiver.getStart().getLine(),
						receiver.getStart().getCharPositionInLine(), receiver.getStop().getCharPositionInLine(), msg);
				typeErrors.add(err);
				validRecT = false;
			}
		} else {
			if (recType.contains(X) && !recTypeFun.contains(X)) {
				env.update(recType, recTypeFun);
			} else if (!recType.contains(X) && recTypeFun.contains(X)) {
				Type tt = env.getType(recType);
				if (tt instanceof DataType) {
					env.update(recTypeFun, recType);
				} else {
					String msg = "Receiver type should be a datatype";

					Error err = ErrorFactory.createError(receiver.getStart().getLine(), receiver.getStart().getLine(),
							receiver.getStart().getCharPositionInLine(), receiver.getStop().getCharPositionInLine(),
							msg);
					typeErrors.add(err);
					validRecT = false;
				}

			} else if (recType.contains(X) && recTypeFun.contains(X)) {
				// both types should be equal
				env.update(recType, recTypeFun);
			}
		}

		boolean hasErr = hasErrors(f.getArguments(), cmFunCall.getExpressionList(), f.getStart().getLine(),
				f.getStart().getLine(), f.getStart().getCharPositionInLine(), f.getStop().getCharPositionInLine());

		return !hasErr && validRecT;
	}

	@Override
	public Boolean visit(Match match) {
		boolean hasError = false;
		// First get all constructors on the left side of cases
		Map<QualifiedName, List<Variable>> allConstructors = getCostOrDest(match);
		// All constructors must belong to the same datatype
		// String typeName = match.getBody().get(0).getName().getqName().getTypeName();
		int sLine = match.getStart().getLine();
		int stLine = match.getStop().getLine();
		int sCol = match.getStart().getCharPositionInLine();
		int stCol = match.getStop().getCharPositionInLine();
		try {
			boolean exprCorr = match.getExpr().accept(this);
			if (exprCorr) {
				String receiverType = match.getExpr().getType();
				String typeName;
				if (match.getqName().getTypeName().contains(X)) {
					if (receiverType.contains(X)) {
						typeName = env.getTypeName(allConstructors, true);
					} else {
						env.update( match.getqName().getTypeName(),receiverType);
						typeName = receiverType;
					}
				} else {
					typeName = match.getqName().getTypeName();
					if (receiverType.contains(X)) {
						env.update(receiverType, typeName);
					} else {
						if (!receiverType.equals(typeName)) {
							hasError = true;
							String msg = "Type mismatch, the receiver type should be " + typeName;
							int sLineE = match.getExpr().getStart().getLine();
							int stLineE = match.getExpr().getStart().getLine();
							int sColE = match.getExpr().getStart().getCharPositionInLine();
							int stColE = match.getExpr().getStop().getCharPositionInLine();

							Error err = ErrorFactory.createError(sLineE, stLineE, sColE, stColE, msg);
							typeErrors.add(err);

							return false;
						}
					}
				}

				boolean areTypesEqual = hasSameType(typeName, allConstructors, match);

				if (areTypesEqual) {
					if (match.getqName().getTypeName().contains(X))
						match.getqName().setTypeName(typeName);

//					if (receiverType.contains(X)) {
//						env.update(receiverType, typeName);
//					} else {
//						if (typeName.contains(X)) {
//							env.update(typeName, receiverType);
//						} else {
//							if (!receiverType.equals(typeName)) {
//								hasError = true;
//								String msg = "Type mismatch, the receiver type should be " + typeName;
//								int sLineE = match.getExpr().getStart().getLine();
//								int stLineE = match.getExpr().getStart().getLine();
//								int sColE = match.getExpr().getStart().getCharPositionInLine();
//								int stColE = match.getExpr().getStop().getCharPositionInLine();
//
//								Error err = ErrorFactory.createError(sLineE, stLineE, sColE, stColE, msg);
//								typeErrors.add(err);
//							}
//						}
//					}

					if (!hasError) {
//						if (exprCorr) {

						if (match.getExpr() instanceof Variable) {
							varsMatchOrCoMatch.add(((Variable) match.getExpr()).getName());
						}

						for (ExprDecl exD : match.getExpressionDeclList()) {
							if (!exD.accept(this))
								hasError = true;
						}
						if (!hasError) {
							boolean isRightSideCorrect = true;
							String inferredType = checkExpressionsMatch(match, isRightSideCorrect);
							if (isRightSideCorrect) {
								if (match.getReturnType().contains(X) && !inferredType.contains(X)) {
									env.update(match.getReturnType(), inferredType);
								} else if (!match.getReturnType().contains(X) && inferredType.contains(X)) {
									env.update(inferredType, match.getReturnType());
								} else if (!match.getReturnType().contains(X) && !inferredType.contains(X)) {
									if (!inferredType.equals(match.getReturnType())) {
										String msg = "Type mismatch, the return type should be " + inferredType;

										Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
										typeErrors.add(err);
									}
								}
							}

						}

//						}
					}

				}
			}

		} catch (DecompositionDiversityException e) {
			String msg = "There is more than one type can be receiver type";

			Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
			typeErrors.add(err);
			hasError = true;
		}

		return !hasError;
	}

	private String checkExpressionsMatch(Match function, boolean isCorrect) {
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
//				cc.getExpr().accept(this);
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
						isCorrect = false;
						String msg = "Type mismatch, the type of expression should be " + type;

						Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
						typeErrors.add(err);
					}
				}

				if (isCorrect) {

					ArrayList<String> temp = new ArrayList<>();
					if (inMatchOrCoMatch) {
						temp.addAll(varsMatchOrCoMatch);
						varsMatchOrCoMatch.clear();
					}

					for (Variable v : cc.getParams()) {
						varsMatchOrCoMatch.add(v.getName());
					}

					inMatchOrCoMatch = true;
					for (ExprDecl ed : function.getExpressionDeclList()) {
						varsMatchOrCoMatch.add(ed.getLeft().getName());
					}

					boolean corr = cc.getExpr().accept(this);
					if (corr && type.contains(X))
						type = cc.getExpr().getType();

					inMatchOrCoMatch = false;
					varsMatchOrCoMatch = temp;

					usedCases.add(cc.getName().getqName().getName());
				}
			} else {
				String msg = "This case is already used and can not be used twice.";

				Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
				typeErrors.add(err);

			}
		}
		return type;
	}

	@Override
	public Boolean visit(Comatch comatch) {
		boolean hasError = false;
		int sLine = comatch.getStart().getLine();
		int stLine = comatch.getStop().getLine();
		int sCol = comatch.getStart().getCharPositionInLine();
		int stCol = comatch.getStop().getCharPositionInLine();
		// First get all destructor on the left side of cocases
		Map<QualifiedName, List<Variable>> allDestructors = getCostOrDest(comatch);
		Map<String, String> desWithReturnTypes = getDesWithRType(comatch);
		// All destructors must belong to the same codatatype
//		String typeName = comatch.getBody().get(0).getName().getqName().getTypeName();
		try {
			String comatchType = comatch.getType();
			String typeName;
			if (comatchType.contains(X)) {
				typeName = env.getTypeName(allDestructors, desWithReturnTypes);
				env.update(comatchType, typeName);
			} else {
				typeName = comatchType;
//				if (typeName.contains(X)) {
//					env.update(typeName, comatchType);
//				} else {
//					if (!comatchType.equals(typeName)) {
//						hasError = true;
//						String msg = "Type mismatch, the return type should be " + typeName;
//
//						Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
//						typeErrors.add(err);
//					}
//				}
			}

			boolean areTypesEqual = hasSameType(typeName, allDestructors, comatch);

			if (areTypesEqual) {

				if (!hasError) {
					for (ExprDecl exD : comatch.getExpressionDeclList()) {
						if (!exD.accept(this))
							hasError = true;
					}
					if (!hasError) {
						checkExpressionsCoMatch(comatch);
					}
				}
			}

		} catch (DecompositionDiversityException e) {
			String msg = "There is more than one type can be type";

			Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
			typeErrors.add(err);
			hasError = true;
		}

		return !hasError;
	}

	private void checkExpressionsCoMatch(Comatch comatch) {
		boolean hasErr = false;
		ArrayList<String> usedCases = new ArrayList<>();
		for (CaseOrCocase cc : comatch.getBody()) {
			int sLine = cc.getStart().getLine();
			int stLine = cc.getStop().getLine();
			int sCol = cc.getStart().getCharPositionInLine();
			int stCol = cc.getStop().getCharPositionInLine();
			if (!usedCases.contains(cc.getName().getqName().getName())) {
				String tn = comatch.getType();
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
					if (!exType.equals(rt)) {
						hasErr = true;
						String msg = "Type mismatch, type of expression " + cc.getExpr().getInfo() + " should be " + rt;
						Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
						typeErrors.add(err);
					}
				}

				if (!hasErr) {

					ArrayList<String> temp = new ArrayList<>();
                    if (inMatchOrCoMatch) {
                        temp.addAll(varsMatchOrCoMatch);
                        varsMatchOrCoMatch.clear();
                    }
                    
					for (Variable v : cc.getParams()) {
						varsMatchOrCoMatch.add(v.getName());
					}

					inMatchOrCoMatch = true;
					for (ExprDecl ed : comatch.getExpressionDeclList()) {
						varsMatchOrCoMatch.add(ed.getLeft().getName());
					}
					cc.getExpr().accept(this);

					inMatchOrCoMatch = false;
					varsMatchOrCoMatch = temp;

					usedCases.add(cc.getName().getqName().getName());
				}

			} else {
				String msg = "This cocase is already used and can not be used twice.";

				Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
				typeErrors.add(err);
			}

		}

	}

	private Map<QualifiedName, List<Variable>> getCostOrDest(MatchOrComatch function) {
		Map<QualifiedName, List<Variable>> res = new HashMap<>();

		for (CaseOrCocase cc : function.getBody()) {
			res.put(cc.getName().getqName(), cc.getParams());
		}
		return res;
	}

	private Map<String, String> getDesWithRType(MatchOrComatch function) {
		Map<String, String> res = new HashMap<>();

		for (CaseOrCocase cc : function.getBody()) {
			res.put(cc.getName().getqName().getName(), cc.getExpr().getType());
		}
		return res;
	}

	private boolean hasSameType(String typeName, Map<QualifiedName, List<Variable>> all, MatchOrComatch function) {
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
			
			if(same) {
				ConstructorOrDestructor cd = env.getConsOrDes(typeName, qn.getName());
				
				for (int i = 0; i < all.get(qn).size(); ++i) {
					String t = all.get(qn).get(i).getType();
					String shouldBe = cd.getTypeNames().get(i);
					if (t.contains(X)) {
						env.update(t, shouldBe);
					} else {
						if (!t.equals(shouldBe)) {
							same = false;
							// TODO err MSG
							String msg = "Argument types are not correct";
							throw new DecompositionDiversityException(msg);
						}
					}

				}
			}
		}
		return same;
	}

	@Override
	public Boolean visit(Let let) {
		
		if(let.getType().contains(X) && !let.getRight().getType().contains(X)) {
			env.update(let.getType(), let.getRight().getType());
		} else {
			env.update(let.getType(), let.getRight().getType());
		}
		
		return let.getLeft().accept(this) && let.getRight().accept(this); 
	}

	@Override
	public Boolean visit(CaseOrCocase caseOrCo) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Boolean visit(ExprDecl exprD) {
		if (exprD.getType().contains(X) || env.lookUp(exprD.getType())) {
			return exprD.getRight().accept(this);
		} else {
			String msg = "Type " + exprD.getType() + " is not declared!";
			int sLine = exprD.getStart().getLine();
			int stLine = exprD.getStop().getLine();
			int sCol = exprD.getStart().getCharPositionInLine();
			int stCol = exprD.getStop().getCharPositionInLine();

			Error err = ErrorFactory.createError(sLine, stLine, sCol, stCol, msg);
			typeErrors.add(err);
			return false;
		}
	}

}
