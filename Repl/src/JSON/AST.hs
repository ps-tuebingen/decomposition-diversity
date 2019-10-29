{-# LANGUAGE DeriveGeneric #-}

module JSON.AST where

import Prelude
import qualified AST
import qualified Names
import Data.Aeson
import GHC.Generics

type Name = Names.Name
type VarName = Names.VarName
type TypeName = Names.TypeName
type QName = Names.QName

data ScopedName
    = Local QName
    | Global QName
    deriving (Generic, Show, Eq)

toCoqScopedName :: ScopedName -> Names.ScopedName
toCoqScopedName (Local qn)  = (Names.Coq_local qn)
toCoqScopedName (Global qn) = (Names.Coq_global qn)

fromCoqScopedName :: Names.ScopedName -> ScopedName
fromCoqScopedName (Names.Coq_local qn)  = (Local qn)
fromCoqScopedName (Names.Coq_global qn) = (Global qn)

data Expr
    = E_Var VarName
    | E_Constr ScopedName [Expr]
    | E_DestrCall ScopedName Expr [Expr]
    | E_FunCall Name [Expr]
    | E_GenFunCall ScopedName [Expr]
    | E_ConsFunCall ScopedName Expr [Expr]
    | E_Match QName Expr
              [ (Expr, TypeName) ]
              [ (ScopedName, Expr) ]
              TypeName
    | E_CoMatch QName 
              [ (Expr, TypeName) ]
              [ (ScopedName, Expr) ]
    | E_Let Expr Expr
    deriving (Generic, Show, Eq)

data FoldExprRecord a = FoldExprRecord
    { f_Var :: VarName -> a,
      f_Constr :: ScopedName -> [a] -> a,
      f_DestrCall :: ScopedName -> a -> [a] -> a,
      f_FunCall :: Name -> [a] -> a,
      f_ComatchFunCall :: ScopedName -> [a] -> a,
      f_MatchFunCall :: ScopedName -> a -> [a] -> a,
      f_Match :: QName -> a ->
                 [(a,TypeName)] ->
                 [(ScopedName, a)] ->
                 TypeName -> a,
      f_CoMatch :: QName -> 
                   [(a,TypeName)] ->
                   [(ScopedName, a)] ->
                   a,
      f_Let :: a -> a -> a }


foldExpr :: FoldExprRecord a -> Expr -> a
foldExpr (FoldExprRecord { f_Var = f}) (E_Var v) =
    f v
foldExpr fr@(FoldExprRecord { f_Constr = f}) (E_Constr sn args) =
    f sn (fmap (foldExpr fr) args)
foldExpr fr@(FoldExprRecord { f_DestrCall = f}) (E_DestrCall sn e args) =
    f sn (foldExpr fr e)
      (fmap (foldExpr fr) args)
foldExpr fr@(FoldExprRecord { f_FunCall = f}) (E_FunCall n args) =
    f n (fmap (foldExpr fr) args)
foldExpr fr@(FoldExprRecord { f_ComatchFunCall = f}) (E_GenFunCall qn args) =
    f qn (fmap (foldExpr fr) args)
foldExpr fr@(FoldExprRecord { f_MatchFunCall = f}) (E_ConsFunCall qn e args) =
    f qn (foldExpr fr e)
      (fmap (foldExpr fr) args)
foldExpr fr@(FoldExprRecord { f_Match = f}) (E_Match qn e bs cs t) =
    f qn (foldExpr fr e)
      foldedBs
      foldedCs
      t
    where foldedBs = fmap (\(e,t) -> (foldExpr fr e, t)) bs
          foldedCs = fmap (\(sn,e) -> (sn, foldExpr fr e)) cs
foldExpr fr@(FoldExprRecord { f_CoMatch = f}) (E_CoMatch qn bs ccs) =
    f qn foldedBs
      foldedCcs
    where foldedBs = fmap (\(e,t) -> (foldExpr fr e, t)) bs
          foldedCcs = fmap (\(sn,e) -> (sn, foldExpr fr e)) ccs
foldExpr fr@(FoldExprRecord { f_Let = f}) (E_Let e1 e2) =
    f (foldExpr fr e1)
      (foldExpr fr e2)

toCoqExprRecord :: FoldExprRecord AST.Coq_expr
toCoqExprRecord = FoldExprRecord {
    f_Var = AST.E_Var,
    f_Constr = AST.E_Constr . toCoqScopedName,
    f_DestrCall = AST.E_DestrCall . toCoqScopedName,
    f_FunCall = AST.E_FunCall,
    f_ComatchFunCall = AST.E_GenFunCall . toCoqScopedName,
    f_MatchFunCall = AST.E_ConsFunCall . toCoqScopedName,
    f_Match = f_Match,
    f_CoMatch = f_CoMatch,
    f_Let = AST.E_Let }
        where
            f_Match qn e bs cs t = AST.E_Match qn e bs (fixScopedNames cs) t
            f_CoMatch qn bs ccs  = AST.E_CoMatch qn bs (fixScopedNames ccs)
            fixScopedNames = fmap (\(sn, e) -> (toCoqScopedName sn, e))
toCoqExpr :: Expr -> AST.Coq_expr
toCoqExpr = foldExpr toCoqExprRecord

data CoqFoldExprRecord a = CoqFoldExprRecord
    { coq_f_Var :: VarName -> a,
      coq_f_Constr :: Names.ScopedName -> [a] -> a,
      coq_f_DestrCall :: Names.ScopedName -> a -> [a] -> a,
      coq_f_FunCall :: Name -> [a] -> a,
      coq_f_ComatchFunCall :: Names.ScopedName -> [a] -> a,
      coq_f_MatchFunCall :: Names.ScopedName -> a -> [a] -> a,
      coq_f_Match :: QName -> a -> 
                 [(a,TypeName)] ->
                 [(Names.ScopedName, a)] ->
                 TypeName -> a,
      coq_f_CoMatch :: QName ->
                   [(a,TypeName)] ->
                   [(Names.ScopedName, a)] ->
                   a,
      coq_f_Let :: a -> a -> a }


coqFoldExpr :: CoqFoldExprRecord a -> AST.Coq_expr -> a
coqFoldExpr (CoqFoldExprRecord { coq_f_Var = f}) (AST.E_Var v) =
    f v
coqFoldExpr fr@(CoqFoldExprRecord { coq_f_Constr = f}) (AST.E_Constr sn args) =
    f sn (fmap (coqFoldExpr fr) args)
coqFoldExpr fr@(CoqFoldExprRecord { coq_f_DestrCall = f}) (AST.E_DestrCall sn e args) =
    f sn (coqFoldExpr fr e)
      (fmap (coqFoldExpr fr) args)
coqFoldExpr fr@(CoqFoldExprRecord { coq_f_FunCall = f}) (AST.E_FunCall n args) =
    f n (fmap (coqFoldExpr fr) args)
coqFoldExpr fr@(CoqFoldExprRecord { coq_f_ComatchFunCall = f}) (AST.E_GenFunCall qn args) =
    f qn (fmap (coqFoldExpr fr) args)
coqFoldExpr fr@(CoqFoldExprRecord { coq_f_MatchFunCall = f}) (AST.E_ConsFunCall qn e args) =
    f qn (coqFoldExpr fr e)
      (fmap (coqFoldExpr fr) args)
coqFoldExpr fr@(CoqFoldExprRecord { coq_f_Match = f}) (AST.E_Match qn e bs cs t) =
    f qn (coqFoldExpr fr e)
      foldedBs
      foldedCs
      t
    where foldedBs = fmap (\(e,t) -> (coqFoldExpr fr e, t)) bs
          foldedCs = fmap (\(sn,e) -> (sn, coqFoldExpr fr e)) cs
coqFoldExpr fr@(CoqFoldExprRecord { coq_f_CoMatch = f}) (AST.E_CoMatch qn bs ccs) =
    f qn foldedBs
      foldedCcs
    where foldedBs = fmap (\(e,t) -> (coqFoldExpr fr e, t)) bs
          foldedCcs = fmap (\(sn,e) -> (sn, coqFoldExpr fr e)) ccs
coqFoldExpr fr@(CoqFoldExprRecord { coq_f_Let = f}) (AST.E_Let e1 e2) =
    f (coqFoldExpr fr e1)
      (coqFoldExpr fr e2)

fromCoqExprRecord :: CoqFoldExprRecord Expr
fromCoqExprRecord = CoqFoldExprRecord {
    coq_f_Var = E_Var,
    coq_f_Constr = E_Constr . fromCoqScopedName,
    coq_f_DestrCall = E_DestrCall . fromCoqScopedName,
    coq_f_FunCall = E_FunCall,
    coq_f_ComatchFunCall = E_GenFunCall . fromCoqScopedName,
    coq_f_MatchFunCall = E_ConsFunCall . fromCoqScopedName,
    coq_f_Match = f_Match,
    coq_f_CoMatch = f_CoMatch,
    coq_f_Let = E_Let }
        where
            f_Match qn e bs cs t = E_Match qn e bs (fixScopedNames cs) t
            f_CoMatch qn bs ccs  = E_CoMatch qn bs (fixScopedNames ccs)
            fixScopedNames = fmap (\(sn, e) -> (fromCoqScopedName sn, e))
fromCoqExpr :: AST.Coq_expr -> Expr
fromCoqExpr = coqFoldExpr fromCoqExprRecord

instance ToJSON ScopedName where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON ScopedName where

instance ToJSON Expr where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON Expr where

