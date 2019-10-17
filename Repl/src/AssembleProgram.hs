module AssembleProgram
  (
    assembleProgram
  ) where

import Names (ScopedName, QName, Name)
import AST (Coq_expr(..))
import HaskellAST
import ProgramDef
import Parser.ParserDefinition
import Parser.Declarations
import Renamer.ParsedToNamed (parsedToNamed)
import Renamer.NamedToDeBruijn (namedToDeBruijn')
import Renamer.DeBruijnToCoq (deBruijnToCoq)
import Data.Foldable (foldrM)
import AssembleSkeleton


type AssembleM = Either String


type FunBod = (Name, Coq_expr)

-- | Add function to program.
addFunToProgram :: FunBod -> Coq_program -> Coq_program
addFunToProgram fb (Coq_mkProgram skel       fun_bods  cfun_bods_g cfun_bods_l gfun_bods_g gfun_bods_l) =
                   (Coq_mkProgram skel (fb : fun_bods) cfun_bods_g cfun_bods_l gfun_bods_g gfun_bods_l)

type GenFunBod = (QName, [(ScopedName, Coq_expr)])

-- | Add generator function to program.
addGenFunToProgram :: GenFunBod -> Coq_program -> Coq_program
addGenFunToProgram gfbod (Coq_mkProgram skel fun_bods cfun_bods_g cfun_bods_l          gfun_bods_g  gfun_bods_l) =
                         (Coq_mkProgram skel fun_bods cfun_bods_g cfun_bods_l (gfbod : gfun_bods_g) gfun_bods_l)

type ConFunBod = (QName, [(ScopedName, Coq_expr)])

-- | Add consumer function to program.
addConFunToProgram :: ConFunBod -> Coq_program -> Coq_program
addConFunToProgram cfbod (Coq_mkProgram skel fun_bods          cfun_bods_g  cfun_bods_l gfun_bods_g gfun_bods_l) =
                         (Coq_mkProgram skel fun_bods (cfbod : cfun_bods_g) cfun_bods_l gfun_bods_g gfun_bods_l)

assembleProgramHelper :: Declaration -> Coq_program -> AssembleM Coq_program
assembleProgramHelper (FunctionD (FNameParse fname) fargs _ ex) pr = do
  renamedExpr <- parsedToNamed (program_skeleton pr) ex
  debruijnExpr <- namedToDeBruijn' (unmapVarNameParse (fst <$> fargs)) renamedExpr
  let coqexpr      = deBruijnToCoq debruijnExpr
  let funbod       = (fname, coqexpr) 
  Right $ addFunToProgram funbod pr
assembleProgramHelper (GenFunD qn fargs cocases) pr = do
  let renameCocase :: (ScopedName, [VarNameParse], ExprParse) -> AssembleM (ScopedName, [String], ExprNamed)
      renameCocase (sn, cargs, expr) = do
        expr' <- parsedToNamed (program_skeleton pr) expr
        Right (sn, unmapVarNameParse cargs, expr')
  renamedCoCases <- sequence (renameCocase <$> cocases)
  let changeToNameless (name,args, e) = do
        e' <- namedToDeBruijn' (args ++ unmapVarNameParse (fst <$> fargs)) e
        Right (name, e')
  debruijnCocases <- sequence (changeToNameless <$>  renamedCoCases)
  let cocasesRes :: [(ScopedName, Coq_expr)]
      cocasesRes = (\(sn, e) -> (sn, deBruijnToCoq e)) <$> debruijnCocases
  Right $ addGenFunToProgram (qn,cocasesRes) pr
assembleProgramHelper (ConFunD qn fargs _rtype cases) pr = do
  let renameCase :: (ScopedName, [VarNameParse], ExprParse) -> AssembleM (ScopedName, [String], ExprNamed)
      renameCase (sn, dargs, expr) = do
        expr' <- parsedToNamed (program_skeleton pr) expr
        Right (sn, unmapVarNameParse dargs, expr')
  renamedCases <- sequence (renameCase <$> cases)
  let changeToNameless (name, args, e) = do
        e' <- namedToDeBruijn' (args ++ unmapVarNameParse (fst <$> fargs)) e
        Right (name, e')
  debruijnCases <- sequence (changeToNameless <$> renamedCases)
  let
    casesRes :: [(ScopedName, Coq_expr)]
    casesRes = (\(sn, e) -> (sn, deBruijnToCoq e)) <$> debruijnCases
  Right $ addConFunToProgram (qn, casesRes) pr
assembleProgramHelper _                 pr = Right pr

-- | Generate a program from a list of declarations.
assembleProgram :: [Declaration] -> Either String Coq_program
assembleProgram decls =
  let
    sk = assembleSkeleton decls
    initialProg = Coq_mkProgram sk [] [] [] [] []
  in
    foldrM assembleProgramHelper initialProg decls

unmapVarNameParse :: [VarNameParse] -> [String]
unmapVarNameParse = fmap (\(VarNameParse tn) -> tn)
