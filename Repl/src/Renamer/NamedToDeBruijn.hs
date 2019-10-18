{-# LANGUAGE ScopedTypeVariables #-}
module Renamer.NamedToDeBruijn
  (
    namedToDeBruijn
  , namedToDeBruijn'
  ) where

import HaskellAST
import Names (TypeName, ScopedName)

lookupName :: [String]              -- ^ A context in which to search
           -> String                -- ^ Named Variable to look up
           -> Either String Integer -- ^ deBruijn Variable or Error
lookupName ctxt var = lookupName' ctxt var 0
  where
    lookupName' [] _ _                       = Left "Used free variable"
    lookupName' (x:ctxt') var i  | x == var  = Right i
                                 | otherwise = lookupName' ctxt' var (i + 1)

-- | Replace named Variables by de Bruijn Variables
namedToDeBruijn :: ExprNamed -> Either String ExprDB
namedToDeBruijn e = namedToDeBruijn' [] e

namedToDeBruijn' :: [String]   -- ^ List of variables in scope. e.g. ["x", "y", "z"]
                  -> ExprNamed -- ^ Named expression
                  -> Either String ExprDB -- ^ Nameless expression or error.
namedToDeBruijn' ctxt (Var y) = do
  i <- lookupName ctxt y
  Right $ Var i
namedToDeBruijn' ctxt (Constr n args) = do
  args' <- sequence (namedToDeBruijn' ctxt <$> args)
  Right $ Constr n args'
namedToDeBruijn' ctxt (DestrCall n e args) = do
  e' <- namedToDeBruijn' ctxt e
  args' <- sequence (namedToDeBruijn' ctxt <$> args)
  Right $ DestrCall n e' args'
namedToDeBruijn' ctxt (FunCall n args) = do
  args' <- sequence (namedToDeBruijn' ctxt <$> args)
  Right $ FunCall n args'
namedToDeBruijn' ctxt (GenFunCall n args) = do
  args' <- sequence (namedToDeBruijn' ctxt <$> args)
  Right $ GenFunCall n args'
namedToDeBruijn' ctxt (ConsFunCall n e args) = do
  e' <- namedToDeBruijn' ctxt e
  args' <- sequence (namedToDeBruijn' ctxt <$> args)
  Right $ ConsFunCall n e' args'
namedToDeBruijn' ctxt (Match n e bl cases rtype) = do
  e' <- namedToDeBruijn' ctxt e
  (bindingNames, bindingList') <- namedToDeBruijnBindingList ctxt bl
  cases' <- sequence (namedToDeBruijnCase bindingNames <$> cases)
  Right (Match n e' bindingList' cases' rtype)
namedToDeBruijn' ctxt (CoMatch n bl cocases) = do
  (bindingNames, bindingList') <- namedToDeBruijnBindingList ctxt bl
  cocases' <- sequence (namedToDeBruijnCase bindingNames <$> cocases)
  Right (CoMatch n bindingList' cocases')
namedToDeBruijn' ctxt (Let x e1 e2) = do
  e1' <- namedToDeBruijn' ctxt e1
  e2' <- namedToDeBruijn' (x:ctxt) e2
  Right $ Let () e1' e2'


-- | Rename a single case in a PatternMatch/CoPatternMatch.
namedToDeBruijnCase :: [String] -- ^ The names of the variables bound in the binding list.
                    -> (ScopedName ,[String],ExprNamed)
                    -> Either String (ScopedName, [()], ExprDB)
namedToDeBruijnCase bindingNames (n, args, e) = do
  let newContext = args ++ bindingNames
  e' <- namedToDeBruijn' newContext e
  Right (n, const () <$> args, e')

-- | Given a context for the expressions in a binding list, and a binding list, return both:
--  - 1) The Names of the variables bound in the bindingList
--  - 2) The renamed bindingList
namedToDeBruijnBindingList :: [String]
    -> [(String, ExprNamed, TypeName)]
    -> Either String ([String], [((),ExprDB,TypeName)])
namedToDeBruijnBindingList ctxt bindingList = do
  let bindingNames = (\(n,_,_) -> n) <$> bindingList
  let bindingListTrans :: (String, ExprNamed, String)
                       -> Either String ((), ExprDB, String)
      bindingListTrans (_n,e,t) = do
        e' <- namedToDeBruijn' ctxt e
        Right $ ((),e',t)
  bindingList' <- sequence (bindingListTrans <$> bindingList)
  return (bindingNames, bindingList')


