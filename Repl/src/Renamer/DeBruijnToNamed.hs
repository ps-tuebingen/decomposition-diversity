module Renamer.DeBruijnToNamed
  (
    deBruijnToNamed'
  , deBruijnToNamed
  ) where

import Names (ScopedName, TypeName, ScopedName(..))
import HaskellAST
-- | Replace de Bruijn Variables by named Variables
deBruijnToNamed :: ExprDB -> Either String ExprNamed
deBruijnToNamed e = deBruijnToNamed' [] e

deBruijnToNamed' :: [String] -> ExprDB -> Either String ExprNamed
deBruijnToNamed' ctxt (Var n) =
  Right $ Var $ (ctxt !! fromInteger n)-- ++ "{" ++ show n ++ "}"
deBruijnToNamed' ctxt (Constr n args) = do
  args' <- sequence (deBruijnToNamed' ctxt <$> args)
  Right $ Constr n args'
deBruijnToNamed' ctxt (DestrCall n e args) = do
  e' <- deBruijnToNamed' ctxt e
  args' <- sequence (deBruijnToNamed' ctxt <$> args)
  Right $ DestrCall n e' args'
deBruijnToNamed' ctxt (FunCall n args) = do
  args' <- sequence (deBruijnToNamed' ctxt <$> args)
  Right $ FunCall n args'
deBruijnToNamed' ctxt (GenFunCall n args) = do
  args' <- sequence (deBruijnToNamed' ctxt <$> args)
  Right $ GenFunCall n args'
deBruijnToNamed' ctxt (ConsFunCall n e args) = do
  e' <- deBruijnToNamed' ctxt e
  args' <- sequence (deBruijnToNamed' ctxt <$> args)
  Right $ ConsFunCall n e' args'
deBruijnToNamed' ctxt (Match n e bindingList cases rtype) = do
  let bindingListNames = genBindingListNames bindingList
  bindingList' <- transBL ctxt bindingList
  e' <- deBruijnToNamed' ctxt e
  cases' <- sequence (deBruijnToNamedCase (length bindingList) bindingListNames <$> cases)
  Right $ Match n e' bindingList' cases' rtype
deBruijnToNamed' ctxt (CoMatch n bindingList cocases) = do
  let bindingListNames = genBindingListNames bindingList
  bindingList' <- transBL ctxt bindingList
  cocases' <- sequence (deBruijnToNamedCase (length bindingList) bindingListNames <$> cocases)
  Right $ CoMatch n bindingList' cocases'
deBruijnToNamed' ctxt (Let _ e1 e2) = do
  let newName = generateName (length ctxt)
  e1' <- deBruijnToNamed' ctxt e1
  e2' <- deBruijnToNamed' (newName : ctxt) e2
  Right $ Let newName e1' e2'

genBindingListNames :: [a] -> [String]
genBindingListNames bl = generateName <$> [0.. length bl - 1]

transBL :: [String]
        -> [((), ExprDB, TypeName)]
        -> Either String [(String, ExprNamed, TypeName)]
transBL ctxt bl = sequence (foo <$> zip bl (genBindingListNames bl))
  where
    foo ((_, e, typename), name) = do
      e' <- deBruijnToNamed' ctxt e
      return (name, e', typename)

deBruijnToNamedCase :: Int -- ^ Length of bindingList
                    -> [String]
                    -> (ScopedName, [()], ExprDB)
                    -> Either String (ScopedName, [String], ExprNamed)
deBruijnToNamedCase i bindingListNames (sn,ls,e) = do
  let caseNames = generateName <$> [ i .. i + length ls - 1]
  e' <- deBruijnToNamed' (caseNames ++ bindingListNames) e
  Right $ (sn, caseNames, e')

