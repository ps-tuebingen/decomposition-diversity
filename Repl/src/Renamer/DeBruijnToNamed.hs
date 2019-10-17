module Renamer.DeBruijnToNamed
  (
    deBruijnToNamed'
  , deBruijnToNamed
  ) where

import Names (ScopedName, TypeName, ScopedName(..))
import HaskellAST
-- | Replace de Bruijn Variables by named Variables
deBruijnToNamed :: ExprDB -> ExprNamed
deBruijnToNamed e = deBruijnToNamed' [] e

deBruijnToNamed' :: [String] -> ExprDB -> ExprNamed
deBruijnToNamed' ctxt (Var n) =
  Var $ (ctxt !! fromInteger n)-- ++ "{" ++ show n ++ "}"
deBruijnToNamed' ctxt (Constr n args) =
  Constr n (deBruijnToNamed' ctxt <$> args)
deBruijnToNamed' ctxt (DestrCall n e args) =
  DestrCall n (deBruijnToNamed' ctxt e) (deBruijnToNamed' ctxt <$> args)
deBruijnToNamed' ctxt (FunCall n args) =
  FunCall n (deBruijnToNamed' ctxt <$> args)
deBruijnToNamed' ctxt (GenFunCall n args) =
  GenFunCall n (deBruijnToNamed' ctxt <$> args)
deBruijnToNamed' ctxt (ConsFunCall n e args) =
  ConsFunCall n (deBruijnToNamed' ctxt e) (deBruijnToNamed' ctxt <$> args)
deBruijnToNamed' ctxt (Match n e bl cases rtype) =
  let
    bindingListNames :: [String]
    bindingListNames = generateName <$> [0.. length bl - 1]
    bindingList :: [(String, ExprNamed, TypeName)]
    bindingList = ((\((_,e,t),n) -> (n,deBruijnToNamed' ctxt e,t)) <$> zip bl bindingListNames)
    foo :: (ScopedName, [()], ExprDB) -> (ScopedName, [String], ExprNamed)
    foo (sn,ls,e) =
      let caseNames = generateName <$> [ length bl .. length bl + length ls - 1] in
      ( sn
      , caseNames
      , deBruijnToNamed' (caseNames ++ bindingListNames) e
      )
  in
    Match n (deBruijnToNamed' ctxt e) bindingList (foo <$> cases) rtype
deBruijnToNamed' ctxt (CoMatch n bl cocases) =
  let
    bindingListNames :: [String]
    bindingListNames = generateName <$> [0..length bl -1] -- Bug territory! BindingList comes later!
    bindingList :: [(String, ExprNamed, TypeName)]
    bindingList = ((\((_,e,t),n) -> (n,deBruijnToNamed' ctxt e,t)) <$> zip bl bindingListNames)
    foo :: (ScopedName, [()], ExprDB) -> (ScopedName, [String], ExprNamed)
    foo (sn,ls,e) =
      let cocaseNames = generateName <$> [ length bl .. length bl + length ls - 1] in
      ( sn
      , cocaseNames
      , deBruijnToNamed' (cocaseNames ++ bindingListNames) e
      )
  in
    CoMatch n bindingList (foo <$>  cocases)
deBruijnToNamed' ctxt (Let _ e1 e2) =
  let newName = generateName (length ctxt) in
    Let newName (deBruijnToNamed' ctxt e1) (deBruijnToNamed' (newName : ctxt) e2)
