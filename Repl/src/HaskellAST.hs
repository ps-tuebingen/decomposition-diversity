module HaskellAST
  (
    Expr(..)
  , ExprNamed
  , ExprDB
  , generateName
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

generatePrefix :: Int -> String
generatePrefix j = chars !! j
  where
    chars = map (:[]) ("xyz" ++ ['a'..'w']) ++ map ('x':) chars

generateName :: Int -> Int -> String
generateName o i = generatePrefix o ++ (show i)

fromToNames :: Int -> Int -> Int -> [String]
fromToNames o i j = generateName o <$> [i..j]
