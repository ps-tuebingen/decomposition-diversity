module Prettyprinter.Declarations
  (
    codatatypesToDoc
  , datatypesToDoc
  , programToDoc
  ) where

import Data.List (intersperse)
import Data.Maybe (fromMaybe)
import Data.Text.Prettyprint.Doc

import AST
import HaskellAST
import Names (QName, ScopedName, TypeName, Name, unscope)
import Prettyprinter.Definitions
import Prettyprinter.Expressions
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
-----------Prettyprint datatypes--------------
---------------------------------------------}

-- | Prettyprint a single constructor.
constructorToDoc :: (ScopedName, [TypeName]) -> PrettyPrinter
constructorToDoc (sn, argts) = do
  ppsn <- scopedNameToDoc sn
  let ppargts = parens (hsep (intersperse comma (pretty <$> argts)))
  return $ ppsn <> ppargts

-- | Prettyprint a single datatype declaration.
datatypeToDoc :: TypeName -> [(ScopedName, [TypeName])] -> PrettyPrinter
datatypeToDoc tn ctors = do
  ppctors <- sequence (constructorToDoc <$> ctors)
  return $
     keyword "data" <+> typename tn <+> keyword "where" <>
     (nest 3 (line <> vcat ppctors))

-- | Select the constructors in the constructorlist which match the typename.
selectCtors :: TypeName -> Coq_ctors -> [(ScopedName, [TypeName])]
selectCtors tn ctors =
  let filteredCtors = filter (\(sn,_) -> fst (unscope sn) == tn) ctors in
  filteredCtors

-- | Prettyprint all datatypes.
datatypesToDoc :: Coq_dts -> Coq_ctors -> PrettyPrinter
datatypesToDoc dts ctors = do
  let dts' = fmap (\tn -> (tn, selectCtors tn ctors)) dts
  ppdts' <- sequence ((\(tn, ctors) -> datatypeToDoc tn ctors) <$> dts')
  return $ vsep ppdts'

{---------------------------------------------
-----------Prettyprint codatatypes------------
---------------------------------------------}

-- | Prettyprint a single destructor.
destructorToDoc :: (ScopedName, [TypeName], TypeName) -> PrettyPrinter
destructorToDoc (sn, argts, rtype) = do
  ppsn <- scopedNameToDoc sn
  let ppargts = parens (hsep (intersperse comma (pretty <$> argts)))
  return $ ppsn <> ppargts <+> colon <+> typename rtype

-- | Prettyprint a single codatatype declaration.
codatatypeToDoc :: TypeName -> [(ScopedName, [TypeName], TypeName)] -> PrettyPrinter
codatatypeToDoc tn dtors = do
  ppdtors <- sequence (destructorToDoc <$> dtors)
  return $
    keyword "codata" <+> typename tn <+> keyword "where" <>
    (nest 3 (line <> vcat ppdtors))

-- | Select the destructors in the destructorlist which match the typename.
selectDtors :: TypeName -> Coq_dtors -> [(ScopedName, [TypeName], TypeName)]
selectDtors tn dtors =
  let filteredDtors = filter (\((sn,_),_) -> fst (unscope sn) == tn) dtors in
  (\((sn,argts),rtype) -> (sn,argts,rtype)) <$> filteredDtors

-- | Prettyprint all codatatypes.
codatatypesToDoc :: Coq_cdts -> Coq_dtors -> PrettyPrinter
codatatypesToDoc cdts dtors = do
  let cdts' = fmap (\tn -> (tn, selectDtors tn dtors)) cdts
  ppcdts' <- sequence ((\(tn, dtors) -> codatatypeToDoc tn dtors) <$> cdts')
  return $ vsep ppcdts'

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
  in
    (\((n, argts), rtype) -> (n, argts, rtype, fromMaybe (error "Could not find function body.") (lookup n funbods))) <$> funsigs

-- | Rename the body of a function declaration into ExprNamed.
renameFunctionDeclaration :: Coq_skeleton -> (Name, [TypeName], TypeName, Coq_expr) -> (Name, [TypeName], TypeName, ExprNamed)
renameFunctionDeclaration sk (n, argts, rtype, body) = (n, argts, rtype, renamedBody)
  where
    renamedBody = deBruijnToNamed' (fromToNames 0 (length argts -1)) (coqToDeBruijn sk body)

-- | Prettyprint a single function declaration.
functionDeclarationToDoc :: Name -> [TypeName] -> TypeName -> ExprNamed -> PrettyPrinter
functionDeclarationToDoc fname argts rtype body = do
  ppbody <- exprToDoc body
  ppargs <- argumentListToDoc argts
  return $
    keyword "function" <+> pretty fname <> ppargs <+> colon <+> typename rtype <+> pretty ":=" <>
    (nest 3 (line <> ppbody))

-- | Prettyprint all function declarations.
functionDeclarationsToDoc :: Coq_program -> PrettyPrinter
functionDeclarationsToDoc prog = do
  let funDecls = selectFunctionDeclarations prog
  let renamedFunDecls = renameFunctionDeclaration (program_skeleton prog) <$> funDecls
  ppRenamedFunDecls <- sequence ((\(n, argts, rtype, body) -> functionDeclarationToDoc n argts rtype body) <$> renamedFunDecls)
  return $ vsep ppRenamedFunDecls

{---------------------------------------------
-----------Prettyprint consumer  functions----
---------------------------------------------}

-- | Select all consumer function declarations in a program.
selectConsumerFunctionDeclarations :: Coq_program -> [(QName, [TypeName], TypeName,[(ScopedName, Coq_expr)])]
selectConsumerFunctionDeclarations prog =
    let
      cfun_sigs_g, cfun_sigs_l :: [((QName, [TypeName]), TypeName)]
      cfun_sigs_g  = skeleton_cfun_sigs_g (program_skeleton prog)
      cfun_sigs_l  = skeleton_cfun_sigs_l (program_skeleton prog)
      cfun_bods_g, cfun_bods_l :: [(QName, [(ScopedName, Coq_expr)])]
      cfun_bods_g = program_cfun_bods_g prog
      cfun_bods_l = program_cfun_bods_l prog
      cfun_decls_g, cfun_decls_l :: [(QName, [TypeName], TypeName,[(ScopedName, Coq_expr)])]
      cfun_decls_g =
        fmap
         (\((qn, argts), rtype) ->
            (qn, argts, rtype, fromMaybe (error "Could not find consumer function body.") (lookup qn cfun_bods_g)))
         cfun_sigs_g
      cfun_decls_l =
        fmap
         (\((qn, argts), rtype) ->
            (qn, argts, rtype, fromMaybe (error "Could not find consumer function body.") (lookup qn cfun_bods_l)))
         cfun_sigs_l
    in
      cfun_decls_g ++ cfun_decls_l

-- | Annotate the Cases with the types of the arguments of the constructors.
renameConsumerFunctionDeclaration1 :: Coq_skeleton
                                   -> (QName, [TypeName], TypeName, [(ScopedName, Coq_expr)])
                                   -> (QName, [TypeName], TypeName, [(ScopedName, [TypeName], Coq_expr)])
renameConsumerFunctionDeclaration1 sk (qn, argts, rtype, cases) = (qn, argts, rtype, cases')
  where
    cases' = (\(sn,e) -> (sn, lookupArgs sn sk, e)) <$> cases

-- | Rename the body inside the cases into ExprNamed.
renameConsumerFunctionDeclaration2 :: Coq_skeleton
                                   -> (QName, [TypeName], TypeName, [(ScopedName, [TypeName], Coq_expr)])
                                   -> (QName, [TypeName], TypeName, [(ScopedName, [TypeName], ExprNamed)])
renameConsumerFunctionDeclaration2 sk (qn, argts, rtype, cases) = (qn, argts, rtype, cases')
  where
    cases' =
      fmap
      (\(sn,argts',e) ->
          (sn, argts', deBruijnToNamed' (fromToNames 1 (length (argts ++ argts'))) (coqToDeBruijn sk e)))
      cases

-- | Prettyprint a single consumer function declaration.
consumerFunctionDeclarationToDoc :: QName -> [TypeName] -> TypeName -> [(ScopedName, [TypeName], ExprNamed)] -> PrettyPrinter
consumerFunctionDeclarationToDoc qn argts rtype cases = do
  ppcases <- sequence (caseToDoc <$> cases)
  ppargs <- argumentListToDoc argts
  return $
    keyword "consumer function" <+>
    typename (fst qn) <> pretty ":" <> pretty (snd qn) <>
    ppargs <+> colon <+> typename rtype <+> pretty ":=" <>
    (nest 3 (line <> (vcat ppcases)))

-- | Prettyprint all consumer function declarations.
consumerFunctionDeclarationsToDoc :: Coq_program -> PrettyPrinter
consumerFunctionDeclarationsToDoc prog = do
  let cfunDecls = selectConsumerFunctionDeclarations prog
  let renamedCfunDecls1 = renameConsumerFunctionDeclaration1 (program_skeleton prog) <$> cfunDecls
  let renamedCfunDecls2 = renameConsumerFunctionDeclaration2 (program_skeleton prog) <$> renamedCfunDecls1
  ppRenamedCfunDecls2 <- sequence
    ((\(qn, argts, rtype, cases) -> consumerFunctionDeclarationToDoc qn argts rtype cases) <$> renamedCfunDecls2)
  return $ vsep ppRenamedCfunDecls2

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
      gfun_decls_g, gfun_decls_l :: [(QName, [TypeName],[(ScopedName, Coq_expr)])]
      gfun_decls_g =
        fmap
         (\(qn, argts) ->
            (qn, argts, fromMaybe (error "Could not find consumer function body.") (lookup qn gfun_bods_g)))
         gfun_sigs_g
      gfun_decls_l =
        fmap
         (\(qn, argts) ->
            (qn, argts, fromMaybe (error "Could not find consumer function body.") (lookup qn gfun_bods_l)))
         gfun_sigs_l
    in
      gfun_decls_g ++ gfun_decls_l

-- | Annotate the Cocases with the types of the arguments of the destructors.
renameGeneratorFunctionDeclaration1 :: Coq_skeleton
                                   -> (QName, [TypeName], [(ScopedName, Coq_expr)])
                                   -> (QName, [TypeName], [(ScopedName, [TypeName], Coq_expr)])
renameGeneratorFunctionDeclaration1 sk (qn, argts, cases) = (qn, argts, cases')
  where
    cases' = (\(sn,e) -> (sn, lookupArgs sn sk, e)) <$> cases

-- | Rename the body inside the cocases into ExprNamed.
renameGeneratorFunctionDeclaration2 :: Coq_skeleton
                                   -> (QName, [TypeName], [(ScopedName, [TypeName], Coq_expr)])
                                   -> (QName, [TypeName], [(ScopedName, [TypeName], ExprNamed)])
renameGeneratorFunctionDeclaration2 sk (qn, argts, cases) = (qn, argts, cases')
  where
    cases' =
      fmap
      (\(sn,argts',e) ->
          (sn, argts', deBruijnToNamed' (fromToNames 1 (length (argts ++ argts'))) (coqToDeBruijn sk e)))
      cases

-- | Prettyprint a single generator function declaration.
generatorFunctionDeclarationToDoc :: QName -> [TypeName] -> [(ScopedName, [TypeName], ExprNamed)] -> PrettyPrinter
generatorFunctionDeclarationToDoc qn argts cocases = do
  ppcocases <- sequence (cocaseToDoc <$> cocases)
  ppargs <- argumentListToDoc argts
  ppqn <- qNameToDoc qn
  return $
    keyword "generator function" <+> ppqn <> ppargs <+> colon <+> typename (fst qn) <+> pretty ":=" <>
    (nest 3 (line <> (vcat ppcocases)))

-- | Prettyprint all generator function declarations.
generatorFunctionDeclarationsToDoc :: Coq_program -> PrettyPrinter
generatorFunctionDeclarationsToDoc prog = do
  let gfunDecls = selectGeneratorFunctionDeclarations prog
  let renamedGfunDecls1 = renameGeneratorFunctionDeclaration1 (program_skeleton prog) <$> gfunDecls
  let renamedGfunDecls2 = renameGeneratorFunctionDeclaration2 (program_skeleton prog) <$> renamedGfunDecls1
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
