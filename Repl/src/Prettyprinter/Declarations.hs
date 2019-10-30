module Prettyprinter.Declarations
  (
    programToDoc
  ) where

import Data.List (intersperse)
import Data.Maybe (fromMaybe)
import Data.Text.Prettyprint.Doc

import AST
import HaskellAST
import Names (QName, ScopedName, TypeName, Name)
import Prettyprinter.Definitions
import Prettyprinter.Expressions
import Prettyprinter.XDataTypes
import ProgramDef
import Renamer.DeBruijnToNamed (deBruijnToNamed')
import Renamer.CoqToDeBruijn (coqToDeBruijn, lookupArgs)
import Skeleton

-- | Print argument list of toplevel declarations.
--  (x1 : T1, .. , xn : Tn)
argumentListToDoc :: [TypeName] -> PrettyPrinter
argumentListToDoc args = do
  let x = (\(n,t) -> pretty (generateName n ++ " : " ++ t)) <$> (zip [0..] args)
  return $ parens (hsep (intersperse comma x))

{---------------------------------------------
-----------Prettyprint function declarations--
---------------------------------------------}

-- | Select all function declarations in a program.
selectFunctionDeclarations :: Coq_program -> [(Name, [TypeName],TypeName,Coq_expr)]
selectFunctionDeclarations prog =
  let
    funsigs :: [((Name,[TypeName]),TypeName)]
    funsigs = skeleton_fun_sigs (program_skeleton prog)
    funbods :: [(Name, Coq_expr)]
    funbods = program_fun_bods prog
    combine ((name, argts), rtype) = ( name
                                     , argts
                                     , rtype
                                     , fromMaybe (error "Could not find function body.") (lookup name funbods)
                                     )
  in
    combine <$> funsigs

-- | Rename the body of a function declaration into ExprNamed.
renameFunctionDeclaration :: Coq_skeleton
                          -> (Name, [TypeName], TypeName, Coq_expr)
                          -> Either String (Name, [TypeName], TypeName, ExprNamed)
renameFunctionDeclaration sk (n, argts, rtype, body) = do
  renamedBody <- coqToDeBruijn sk body
  renamedBody' <- deBruijnToNamed' (fromToNames 0 (length argts -1)) renamedBody
  return (n, argts, rtype, renamedBody')

-- | Prettyprint a single function declaration.
functionDeclarationToDoc :: Name -> [TypeName] -> TypeName -> ExprNamed -> PrettyPrinter
functionDeclarationToDoc fname argts rtype body = do
  ppbody <- exprToDoc body
  ppargs <- argumentListToDoc argts
  return $
    keyword "fun" <+> pretty fname <> ppargs <+> colon <+> typename rtype <+> pretty ":=" <>
    (nest 3 (line <> ppbody))

-- | Prettyprint all function declarations.
functionDeclarationsToDoc :: Coq_program -> PrettyPrinter
functionDeclarationsToDoc prog = do
  let funDecls = selectFunctionDeclarations prog
  let renameFunctionDeclaration' = (either (error "Renaming Function declaration failed") id) . (renameFunctionDeclaration (program_skeleton prog))
  let renamedFunDecls = renameFunctionDeclaration' <$> funDecls
  ppRenamedFunDecls <- sequence ((\(n, argts, rtype, body) -> functionDeclarationToDoc n argts rtype body) <$> renamedFunDecls)
  return $ vsep ppRenamedFunDecls

{---------------------------------------------
-----------Prettyprint consumer  functions----
---------------------------------------------}

-- | Select all consumer function declarations in a program.
selectConsumerFunctionDeclarations :: Coq_program
                                   -> Either String [(QName, [TypeName], TypeName,[(ScopedName, Coq_expr)])]
selectConsumerFunctionDeclarations prog =
    let
      cfun_sigs_g, cfun_sigs_l :: [((QName, [TypeName]), TypeName)]
      cfun_sigs_g  = skeleton_cfun_sigs_g (program_skeleton prog)
      cfun_sigs_l  = skeleton_cfun_sigs_l (program_skeleton prog)
      cfun_bods_g, cfun_bods_l :: [(QName, [(ScopedName, Coq_expr)])]
      cfun_bods_g = program_cfun_bods_g prog
      cfun_bods_l = program_cfun_bods_l prog
      combine bods ((qn, argts), rtype) = ( qn
                                    , argts
                                    , rtype
                                    , fromMaybe (error "Could not find consumer function body.") (lookup qn bods))
      cfun_decls_g, cfun_decls_l :: [(QName, [TypeName], TypeName,[(ScopedName, Coq_expr)])]
      cfun_decls_g = fmap (combine cfun_bods_g) cfun_sigs_g
      cfun_decls_l = fmap (combine cfun_bods_l) cfun_sigs_l
    in
      return $ cfun_decls_g ++ cfun_decls_l

-- | Annotate the Cases with the types of the arguments of the constructors.
renameConsumerFunctionDeclaration1 :: Coq_skeleton
                                   -> (QName, [TypeName], TypeName, [(ScopedName, Coq_expr)])
                                   -> Either String (QName, [TypeName], TypeName, [(ScopedName, [TypeName], Coq_expr)])
renameConsumerFunctionDeclaration1 sk (qn, argts, rtype, cases) = do
    let f (sn, e) = do
          args <- lookupArgs sn sk
          return (sn, args, e)
    cases' <- sequence $ f <$> cases
    return (qn, argts, rtype, cases')

-- | Rename the body inside the cases into ExprNamed.
renameConsumerFunctionDeclaration2 :: Coq_skeleton
                                   -> (QName, [TypeName], TypeName, [(ScopedName, [TypeName], Coq_expr)])
                                   -> Either String (QName, [TypeName], TypeName, [(ScopedName, [TypeName], ExprNamed)])
renameConsumerFunctionDeclaration2 sk (qn, argts, rtype, cases) = do
  let f (sn, argts', e) = do
        eDB <- coqToDeBruijn sk e
        let nameArg1 = fromToNames 0              (length argts - 1)
        let nameArg2 = fromToNames (length argts) (length (argts ++ argts') - 1)
        eN <- deBruijnToNamed'  (nameArg2 ++ nameArg1) eDB
        return (sn,nameArg2 , eN)
  cases' <- sequence $ f <$> cases
  return (qn, argts, rtype, cases')

collectRenamedFunctionDecls :: Coq_program -> Either String [(QName, [TypeName], TypeName, [(ScopedName, [TypeName], ExprNamed)])]
collectRenamedFunctionDecls prog = do
  cfunDecls <- selectConsumerFunctionDeclarations prog
  renamedCfunDecls1 <- sequence $ renameConsumerFunctionDeclaration1 (program_skeleton prog) <$> cfunDecls
  sequence $ renameConsumerFunctionDeclaration2 (program_skeleton prog) <$> renamedCfunDecls1

-- | Prettyprint a single consumer function declaration.
consumerFunctionDeclarationToDoc :: QName -> [TypeName] -> TypeName -> [(ScopedName, [TypeName], ExprNamed)] -> PrettyPrinter
consumerFunctionDeclarationToDoc qn argts rtype cases = do
  ppcases <- sequence (caseToDoc <$> cases)
  ppargs <- argumentListToDoc argts
  return $
    keyword "cfun" <+>
    typename (fst qn) <> pretty ":" <> pretty (snd qn) <>
    ppargs <+> colon <+> typename rtype <+> pretty ":=" <>
    (nest 3 (line <> (vcat ppcases)))

-- | Prettyprint all consumer function declarations.
consumerFunctionDeclarationsToDoc :: Coq_program -> PrettyPrinter
consumerFunctionDeclarationsToDoc prog = do
  let renamedCfunDecls = either (error "consumerFunctionDeclarationsToDoc") id $ collectRenamedFunctionDecls prog
  ppRenamedCfunDecls <- sequence
    ((\(qn, argts, rtype, cases) -> consumerFunctionDeclarationToDoc qn argts rtype cases) <$> renamedCfunDecls)
  return $ vsep ppRenamedCfunDecls

{---------------------------------------------
-----------Prettyprint generator functions----
---------------------------------------------}

-- | Select all generator function declarations in a program.
selectGeneratorFunctionDeclarations :: Coq_program -> [(QName, [TypeName], [(ScopedName, Coq_expr)])]
selectGeneratorFunctionDeclarations prog =
    let
      gfun_sigs_g, gfun_sigs_l :: [(QName, [TypeName])]
      gfun_sigs_g  = skeleton_gfun_sigs_g (program_skeleton prog)
      gfun_sigs_l  = skeleton_gfun_sigs_l (program_skeleton prog)
      gfun_bods_g, gfun_bods_l :: [(QName, [(ScopedName, Coq_expr)])]
      gfun_bods_g = program_gfun_bods_g prog
      gfun_bods_l = program_gfun_bods_l prog
      combine bods (qn, argts) = ( qn
                                 , argts
                                 , fromMaybe (error "Could not find consumer function body.") (lookup qn bods)
                                 )
      gfun_decls_g, gfun_decls_l :: [(QName, [TypeName],[(ScopedName, Coq_expr)])]
      gfun_decls_g = fmap (combine gfun_bods_g) gfun_sigs_g
      gfun_decls_l = fmap (combine gfun_bods_l) gfun_sigs_l
    in
      gfun_decls_g ++ gfun_decls_l

-- | Annotate the Cocases with the types of the arguments of the destructors.
renameGeneratorFunctionDeclaration1 :: Coq_skeleton
                                   -> (QName, [TypeName], [(ScopedName, Coq_expr)])
                                   -> Either String (QName, [TypeName], [(ScopedName, [TypeName], Coq_expr)])
renameGeneratorFunctionDeclaration1 sk (qn, argts, cases) = do
  let lookupArgs' (sn, e) = do
        args <- lookupArgs sn sk
        return (sn, args, e)
  cases' <- sequence $ lookupArgs' <$> cases
  return (qn, argts, cases')

-- | Rename the body inside the cocases into ExprNamed.
renameGeneratorFunctionDeclaration2 :: Coq_skeleton
                                   -> (QName, [TypeName], [(ScopedName, [TypeName], Coq_expr)])
                                   -> Either String (QName, [TypeName], [(ScopedName, [TypeName], ExprNamed)])
renameGeneratorFunctionDeclaration2 sk (qn, argts, cases) = do
  let f (sn,argts', e) = do
        eDB <- coqToDeBruijn sk e
        let nameArg1 = fromToNames 0              (length argts - 1)
        let nameArg2 = fromToNames (length argts) (length (argts ++ argts') - 1)
        eN <- deBruijnToNamed' (nameArg2 ++ nameArg1) eDB
        return (sn, nameArg2, eN)
  cases' <- sequence $ f <$> cases
  return (qn, argts, cases')

-- | Prettyprint a single generator function declaration.
generatorFunctionDeclarationToDoc :: QName -> [TypeName] -> [(ScopedName, [TypeName], ExprNamed)] -> PrettyPrinter
generatorFunctionDeclarationToDoc qn argts cocases = do
  ppcocases <- sequence (cocaseToDoc <$> cocases)
  ppargs <- argumentListToDoc argts
  ppqn <- qNameToDoc qn
  return $
    keyword "gfun" <+> ppqn <> ppargs <+> colon <+> typename (fst qn) <+> pretty ":=" <>
    (nest 3 (line <> (vcat ppcocases)))

-- | Prettyprint all generator function declarations.
generatorFunctionDeclarationsToDoc :: Coq_program -> PrettyPrinter
generatorFunctionDeclarationsToDoc prog = do
  let gfunDecls = selectGeneratorFunctionDeclarations prog
  let renamedGfunDecls1 = either (error "foo") id $ sequence $ renameGeneratorFunctionDeclaration1 (program_skeleton prog) <$> gfunDecls
  let renamedGfunDecls2 = either (error "foo") id $ sequence $ renameGeneratorFunctionDeclaration2 (program_skeleton prog) <$> renamedGfunDecls1
  ppRenamedGfunDecls2 <- sequence
    ((\(qn, argts, cocases) -> generatorFunctionDeclarationToDoc qn argts cocases) <$> renamedGfunDecls2)
  return $ vsep ppRenamedGfunDecls2

{---------------------------------------------
-----------Prettyprint whole program----------
---------------------------------------------}
-- | Prettyprint the whole program.
programToDoc :: Coq_program -> PrettyPrinter
programToDoc prog = do
  let progSkeleton = program_skeleton prog
  dts   <- datatypesToDoc   (skeleton_dts  progSkeleton) (skeleton_ctors progSkeleton)
  cdts  <- codatatypesToDoc (skeleton_cdts progSkeleton) (skeleton_dtors progSkeleton)
  funs  <- functionDeclarationsToDoc          prog
  cfuns <- consumerFunctionDeclarationsToDoc  prog
  gfuns <- generatorFunctionDeclarationsToDoc prog
  return $
    dts   <> line <> line <>
    cdts  <> line <> line <>
    funs  <> line <> line <>
    cfuns <> line <> line <>
    gfuns
