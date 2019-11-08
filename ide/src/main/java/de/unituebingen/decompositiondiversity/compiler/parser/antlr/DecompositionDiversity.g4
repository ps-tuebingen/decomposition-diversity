grammar DecompositionDiversity;

prog: imports? def* EOF ;

imports: importDecl* ;

importDecl: importR | importD;

importR : 'import' type=UNAME ':' 'R';

importD : 'import' type=UNAME ':' 'D';

def: typeDeclarations | functionDeclarations ;

/*
* Data type and codata type 
* declaration
*/
typeDeclarations: dataTypeDecl | codataTypeDecl ;

dataTypeDecl: dataTypeDeclHeader dataTypeDeclBody ;

codataTypeDecl: codataTypeDeclHeader codataTypeDeclBody ;

dataTypeDeclHeader: 'data' name=UNAME 'where' ;

dataTypeDeclBody: constructorDecl* ;

constructorDecl: name=UNAME '(' typeList? ')' ;

codataTypeDeclHeader: 'codata' type=UNAME 'where' ;

codataTypeDeclBody: (destructorDecl)* ;

destructorDecl: name=LNAME '(' typeList? ')' ':' returnType ;

typeList: type=UNAME | typeList ',' type=UNAME ;

/*
* Functions declaration
*/
functionDeclarations: functionDecl | consumerFunctionDecl | generatorFunctionDecl ;

/*
* Function
*
* function xyz(arg)
*/
functionDecl: functionHeader funBody ;

functionHeader: 'fun' name=LNAME '(' varDeclList? ')' (':' returnType)? IS ;

funBody: expression ;

varDeclList: varDecl | varDeclList ',' varDecl ;

IS: ':=' ;
/*
* Consumer Function
*/
consumerFunctionDecl: consumerFunHeader consumerFunBody ;

consumerFunHeader: 'cfun' (receiverType ':')? name=LNAME argumentListCons (':' returnType)? IS ;

argumentListCons: '(' varDeclList? ')' ;

consumerFunBody: caseStmt* ;

caseStmt: 'case' caseConst '=>' expression ;

caseConst: name=UNAME '(' varList? ')' ; 


/*
* Generator Function
*/
generatorFunctionDecl: generatorFunHeader generatorFunBody ;

generatorFunHeader: KWGEN name=UNAME argumentListGen (':' returnType)? IS ;

KWGEN: 'gfun';

argumentListGen: '(' varDeclList? ')';

generatorFunBody: cocase* ;

cocase: 'cocase' cocaseDestr '=>' expression ;

cocaseDestr: name=LNAME '(' varList? ')' ; 

varList: name=LNAME | varList ',' name=LNAME ;

varDecl: name=LNAME ':' type=UNAME ;

receiverType: type=UNAME ;

returnType: type=UNAME ;

/*
* Expression
*/

expression: var=LNAME #VarExpr
			| ogenCall=genCall #GenCallExpr
			| ofunCall=funCall #FunCallExpr
			| expression '.' consCall=LNAME '(' expressionList? ')' #ConsCallExpr
			| matchExpr=match #MatchExpr
			| comatchExpr=comatch #ComatchExpr
			| letExpr=let	#LetExpr
			| nat=NATNUM #Nat
			| lambda #LambdaExpr
			;

lambda: '(' var=LNAME ':' type=UNAME ')' '=>' expression;

NATNUM: zero='0' | nZero=NONZERODIGIT;

fragment
NONZERODIGIT: [1-9][0-9]*; 

funCall: name=LNAME '(' expressionList? ')' ;

genCall: name=UNAME '(' expressionList? ')' ;

match: 'match' (type=UNAME ':')? name=LNAME expression ('using' expressionDeclList)? ('returning' rt=UNAME )? 'with' caseStmt+ ;

comatch: 'comatch' (type=UNAME ':')? name=UNAME ('using' expressionDeclList)? 'with' cocase+ ;

let: 'let' assignVar 'in' expression ;

assignVar: name=LNAME ':=' expression ;

expressionList: expression | expressionList ',' expression ;

expressionDeclList:  exprDecl | expressionDeclList ',' exprDecl ;

exprDecl: assignVar (':' type=UNAME)?;

UNAME: '_'?[A-Z][a-zA-Z0-9]* ;

LNAME: '_'?[a-z][a-zA-Z0-9]* ;

TRANS: 'R' | 'D' ;

//
// Whitespace and comments
//

WS  :  [ \t\r\n\u000C]+ -> skip
    ;

COMMENT
    :   '/*' .*? '*/' -> skip
    ;

LINE_COMMENT
    :   '//' ~[\r\n]* -> skip
    ;
