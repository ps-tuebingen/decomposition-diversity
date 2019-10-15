{-# LANGUAGE ScopedTypeVariables #-}
module HaskellAST where
import Names (VarName, ScopedName, TypeName, QName, Name, ScopedName(..))
import AST
import Skeleton
import Plumbing ()
import Debug.Trace


 
-- | Handwritten, parameterized, version of the extracted type "Coq_expr"
-- Arguments:
-- var = type of variables (Int for deBruijn, String for Named Variables)
-- bind = type of binding sites (Unit for deBruijn, String for Named Variables)
data Expr var bind
  = Var var
  | Constr ScopedName [Expr var bind]
  | DestrCall ScopedName (Expr var bind) [Expr var bind]
  | FunCall Name [(Expr var bind)]
  | GenFunCall ScopedName [Expr var bind]
  | ConsFunCall ScopedName (Expr var bind) [Expr var bind]
  | Match QName (Expr var bind) [(bind, Expr var bind, TypeName)] [(ScopedName, [bind], Expr var bind)] TypeName
  | CoMatch QName [(bind, Expr var bind, TypeName)] [(ScopedName,[bind], Expr var bind)]
  | Let bind (Expr var bind) (Expr var bind)

-- De Bruijn Version
-- Important: In the case of "[bind]" in th AST, the correct number of "()" should be in the list!
type ExprDB    = Expr VarName ()

-- Named Version
type ExprNamed = Expr String  String

-- | Check whether all variables in a ExprDB are bound.
checkClosed :: Integer -> ExprDB -> Bool
checkClosed n (Var m) = n <= m
checkClosed n (Constr _ args) = all (==True) (checkClosed n <$> args)
checkClosed n (DestrCall _ e args) = all (==True) (checkClosed n <$> (e:args))
checkClosed n (FunCall _ args) = all (==True) (checkClosed n <$> args)
checkClosed n (GenFunCall _ args) = all (==True) (checkClosed n <$> args)
checkClosed n (ConsFunCall _ e args) = all (==True) (checkClosed n <$> (e:args))
checkClosed n (Match _ e bl cases _) =
  (all (==True) ((\(_,ex,_) -> checkClosed n ex) <$> bl))
  &&
  (checkClosed n e)
  &&
  (all (==True) ((\(_,bs,ex) -> checkClosed (toInteger (length bl + length bs)) ex) <$> cases))
checkClosed n (CoMatch _ bl cases) =
  (all (==True) ((\(_,e,_) -> checkClosed n e) <$> bl))
  &&
  (all (==True) ((\(_,bs,e) -> checkClosed (toInteger (length bl + length bs)) e) <$> cases))
checkClosed n (Let _ e1 e2) = checkClosed n e1 && checkClosed (n + 1) e2

{---------------------------------------------
-----------Coq_expr <-> ExprDB  --------------
---------------------------------------------}

-- | Convert a ExprDB into a Coq_expr.
exprDB2CoqExpr :: ExprDB -> Coq_expr
exprDB2CoqExpr (Var n) = E_Var n
exprDB2CoqExpr (Constr n args) = E_Constr n (exprDB2CoqExpr <$> args)
exprDB2CoqExpr (DestrCall n e args) = E_DestrCall n (exprDB2CoqExpr e) (exprDB2CoqExpr <$> args)
exprDB2CoqExpr (FunCall n args) = E_FunCall n (exprDB2CoqExpr <$> args)
exprDB2CoqExpr (GenFunCall n args) = E_GenFunCall n (exprDB2CoqExpr <$> args)
exprDB2CoqExpr (ConsFunCall n e args) = E_ConsFunCall n (exprDB2CoqExpr e) (exprDB2CoqExpr <$> args)
exprDB2CoqExpr (Match n e bl cases rtype) =
  E_Match n (exprDB2CoqExpr e)
  ((\(_,e,n) -> (exprDB2CoqExpr e, n)) <$> bl) -- Binding List
  ((\(n,_,e) -> (n, exprDB2CoqExpr e)) <$> cases) -- Cases
  rtype
exprDB2CoqExpr (CoMatch n bl cocases) =
  E_CoMatch n
  ((\(_,e,n) -> (exprDB2CoqExpr e, n)) <$> bl) -- Binding List
  ((\(n,_,e) -> (n, exprDB2CoqExpr e)) <$> cocases) -- Cocases
exprDB2CoqExpr (Let _ e1 e2) = E_Let (exprDB2CoqExpr e1) (exprDB2CoqExpr e2)

-- | Convert a Coq_expr into a ExprDB.
-- An ExprDB contains more information than a Coq_expr, since the locations of
-- binding occurrances are explicitly marked with "()" in matches and comatches.
coqExpr2exprDB :: Coq_skeleton -> Coq_expr -> ExprDB
coqExpr2exprDB _  (E_Var n) =
  Var n
coqExpr2exprDB sk (E_Constr n args) =
  Constr n (coqExpr2exprDB sk <$> args)
coqExpr2exprDB sk (E_DestrCall n e args) =
  DestrCall n (coqExpr2exprDB sk e) (coqExpr2exprDB sk <$> args)
coqExpr2exprDB sk (E_FunCall n args) =
  FunCall n (coqExpr2exprDB sk <$> args)
coqExpr2exprDB sk (E_GenFunCall n args) =
  GenFunCall n (coqExpr2exprDB sk <$> args)
coqExpr2exprDB sk (E_ConsFunCall n e args) =
  ConsFunCall n (coqExpr2exprDB sk e) (coqExpr2exprDB sk <$> args)
coqExpr2exprDB sk (E_Match n e bl cases rtype) =
  let
    newBindingList :: [((),ExprDB, TypeName)]
    newBindingList = (\(e,tn) -> ((),coqExpr2exprDB sk e,tn)) <$> bl
    newCases :: [(ScopedName, [()], ExprDB)]
    newCases = (\(sn,e) -> (sn,replicate (lookupNumArgs sn sk) (),coqExpr2exprDB sk e)) <$> cases
  in
  Match n (coqExpr2exprDB sk e) newBindingList newCases rtype
coqExpr2exprDB sk (E_CoMatch n bl cocases) =
  let
    newBindingList :: [((),ExprDB, TypeName)]
    newBindingList = (\(e,tn) -> ((),coqExpr2exprDB sk e,tn)) <$> bl
    newCocases :: [(ScopedName, [()], ExprDB)]
    newCocases = (\(sn,e) -> (sn,replicate (lookupNumArgs sn sk) (),coqExpr2exprDB sk e)) <$> cocases
  in
  CoMatch n newBindingList newCocases
coqExpr2exprDB sk (E_Let e1 e2) =
  Let () (coqExpr2exprDB sk e1) (coqExpr2exprDB sk e2)


lookupScopedNamesSkeleton :: Coq_skeleton -> [(ScopedName, [TypeName])]
lookupScopedNamesSkeleton sk =
  let
    ctors = (skeleton_ctors sk)
    dtors = (\((sn,args),_) -> (sn, args)) <$> (skeleton_dtors sk)
  in
    ctors ++ dtors

lookupArgs :: ScopedName -> Coq_skeleton -> [TypeName]
lookupArgs sn sk = case lookup sn (lookupScopedNamesSkeleton sk) of
  Just args -> args
  Nothing -> error "lookupNumArgs: ScopedName not in skeleton"

lookupNumArgs :: ScopedName -> Coq_skeleton -> Int
lookupNumArgs sn sk =
  let scopedNames = (lookupScopedNamesSkeleton sk) in
  case (lookup sn scopedNames) of
    Just args -> length args
    Nothing -> error $ "lookupNumArgs: ScopedName " ++ show sn ++ " not in skeleton"

{---------------------------------------------
-----------ExprDB <-> ExprNamed  --------------
---------------------------------------------}

generateName :: Int -> String
generateName i = "x" ++ (show i)

fromToNames :: Int -> Int -> [String]
fromToNames i j = generateName <$> [i..j]

-- | Replace de Bruijn Variables by named Variables
exprDB2exprNamed :: ExprDB -> ExprNamed
exprDB2exprNamed e = exprDB2exprNamed' [] e



exprDB2exprNamed' :: [String] -> ExprDB -> ExprNamed
exprDB2exprNamed' ctxt (Var n) =
  Var $ (ctxt !! fromInteger n)-- ++ "{" ++ show n ++ "}"
exprDB2exprNamed' ctxt (Constr n args) =
  Constr n (exprDB2exprNamed' ctxt <$> args)
exprDB2exprNamed' ctxt (DestrCall n e args) =
  DestrCall n (exprDB2exprNamed' ctxt e) (exprDB2exprNamed' ctxt <$> args)
exprDB2exprNamed' ctxt (FunCall n args) =
  FunCall n (exprDB2exprNamed' ctxt <$> args)
exprDB2exprNamed' ctxt (GenFunCall n args) =
  GenFunCall n (exprDB2exprNamed' ctxt <$> args)
exprDB2exprNamed' ctxt (ConsFunCall n e args) =
  ConsFunCall n (exprDB2exprNamed' ctxt e) (exprDB2exprNamed' ctxt <$> args)
exprDB2exprNamed' ctxt (Match n e bl cases rtype) =
  let
    bindingListNames :: [String]
    bindingListNames = generateName <$> [0.. length bl - 1]
    bindingList :: [(String, ExprNamed, TypeName)]
    bindingList = ((\((_,e,t),n) -> (n,exprDB2exprNamed' ctxt e,t)) <$> zip bl bindingListNames)
    foo :: (ScopedName, [()], ExprDB) -> (ScopedName, [String], ExprNamed)
    foo (sn,ls,e) =
      let caseNames = generateName <$> [ length bl .. length bl + length ls - 1] in
      ( sn
      , caseNames
      , exprDB2exprNamed' (caseNames ++ bindingListNames) e
      )
  in
    Match n (exprDB2exprNamed' ctxt e) bindingList (foo <$> cases) rtype
exprDB2exprNamed' ctxt (CoMatch n bl cocases) =
  let
    bindingListNames :: [String]
    bindingListNames = generateName <$> [0..length bl -1] -- Bug territory! BindingList comes later!
    bindingList :: [(String, ExprNamed, TypeName)]
    bindingList = ((\((_,e,t),n) -> (n,exprDB2exprNamed' ctxt e,t)) <$> zip bl bindingListNames)
    foo :: (ScopedName, [()], ExprDB) -> (ScopedName, [String], ExprNamed)
    foo (sn,ls,e) =
      let cocaseNames = generateName <$> [ length bl .. length bl + length ls - 1] in
      ( sn
      , cocaseNames
      , exprDB2exprNamed' (cocaseNames ++ bindingListNames) e
      )
  in
    CoMatch n bindingList (foo <$>  cocases)
exprDB2exprNamed' ctxt (Let _ e1 e2) =
  let newName = generateName (length ctxt) in
    Let newName (exprDB2exprNamed' ctxt e1) (exprDB2exprNamed' (newName : ctxt) e2)


lookupName :: Eq a
           => [a] -- ^ Context
           -> a   -- ^ Named Variable to look up
           -> Either String Int -- ^ deBruijn Variable or Error
lookupName ls y = lookupName' ls y 0
  where
    lookupName' [] _ _ = Left "Used free variable"
    lookupName' (x:xs) z i =
      if x == z
      then Right i
      else lookupName' xs z (i + 1)

-- | Replace named Variables by de Bruijn Variables
exprNamed2exprDB :: ExprNamed -> Either String ExprDB
exprNamed2exprDB e = exprNamed2exprDB' [] e

exprNamed2exprDB' :: forall a. Eq a
                  => [a] -- ^ List of variables in scope. e.g. ["x", "y", "z"]
                  -> Expr a a -- ^ Named expression
                  -> Either String ExprDB -- ^ Nameless expression or error.
exprNamed2exprDB' ctxt (Var y) = do
  i <- lookupName ctxt y
  Right $ Var (toInteger $ i)
exprNamed2exprDB' ctxt (Constr n args) = do
  args' <- sequence (exprNamed2exprDB' ctxt <$> args)
  Right $ Constr n args'
exprNamed2exprDB' ctxt (DestrCall n e args) = do
  e' <- exprNamed2exprDB' ctxt e
  args' <- sequence (exprNamed2exprDB' ctxt <$> args)
  Right $ DestrCall n e' args'
exprNamed2exprDB' ctxt (FunCall n args) = do
  args' <- sequence (exprNamed2exprDB' ctxt <$> args)
  Right $ FunCall n args'
exprNamed2exprDB' ctxt (GenFunCall n args) = do
  args' <- sequence (exprNamed2exprDB' ctxt <$> args)
  Right $ GenFunCall n args'
exprNamed2exprDB' ctxt (ConsFunCall n e args) = do
  e' <- exprNamed2exprDB' ctxt e
  args' <- sequence (exprNamed2exprDB' ctxt <$> args)
  Right $ ConsFunCall n e' args'
exprNamed2exprDB' ctxt (Match n e bl cases rtype) = do
  e' <- exprNamed2exprDB' ctxt e
  let bindingNames = (\(n,_,_) -> n) <$> bl
  let blTrans :: (a, Expr a a, String) -> Either String ((), ExprDB, String)
      blTrans (n,e,t) = do
        e' <- exprNamed2exprDB' ctxt e
        Right $ ((),e',t)
  bl' <- sequence (blTrans <$> bl)
  let caseTrans :: (b ,[a],Expr a a) -> Either String (b, [()], ExprDB)
      caseTrans (n, args, e) = do
        e' <- exprNamed2exprDB' (args ++ bindingNames) e -- Bug territory! args should be closer
        Right (n, const () <$> args, e')
  cases' <- sequence (caseTrans <$> cases)
  Right (Match n e' bl' cases' rtype)
exprNamed2exprDB' ctxt (CoMatch n bl cocases) = do
  let bindingNames = (\(n,_,_) -> n) <$> bl
  let blTrans :: (a, Expr a a, String) -> Either String ((), ExprDB, String)
      blTrans (n,e,t) = do
        e' <- exprNamed2exprDB' ctxt e
        Right $ ((),e',t)
  bl' <- sequence (blTrans <$> bl)
  let cocaseTrans :: (b ,[a],Expr a a) -> Either String (b, [()], ExprDB)
      cocaseTrans (n, args, e) = do
        e' <- exprNamed2exprDB' (args ++ bindingNames) e
        Right (n, const () <$> args, e')
  cocases' <- sequence (cocaseTrans <$> cocases)
  Right (CoMatch n bl' cocases')
exprNamed2exprDB' ctxt (Let x e1 e2) = do
  e1' <- exprNamed2exprDB' ctxt e1
  e2' <- exprNamed2exprDB' (x:ctxt) e2
  Right $ Let () e1' e2'
  
