module Renamer.DeBruijnToNamed
  (
    -- DeBruijn to Named
    exprDB2exprNamed'
  , exprDB2exprNamed
  ) where

import Names (ScopedName, TypeName, ScopedName(..))
import HaskellAST
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
