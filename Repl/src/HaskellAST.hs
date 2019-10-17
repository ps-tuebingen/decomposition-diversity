{-# LANGUAGE ScopedTypeVariables #-}
module HaskellAST
  (
    Expr(..)
  , ExprNamed
  , ExprDB
  , generateName
  -- Named to DeBruijn
  , exprNamed2exprDB
  , exprNamed2exprDB'
  , fromToNames
  ) where
import Names (VarName, ScopedName, TypeName, QName, Name, ScopedName(..))
import Plumbing ()

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
-----------ExprDB <-> ExprNamed  --------------
---------------------------------------------}

generateName :: Int -> String
generateName i = "x" ++ (show i)

fromToNames :: Int -> Int -> [String]
fromToNames i j = generateName <$> [i..j]



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
      blTrans (_n,e,t) = do
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
      blTrans (_n,e,t) = do
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
  
