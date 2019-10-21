module Prettyprinter.XDataTypes
  ( codatatypesToDoc
  , datatypesToDoc
  ) where

import Data.List (intersperse)
import Data.Text.Prettyprint.Doc

import Names (ScopedName, TypeName, unscope)
import Prettyprinter.Definitions
import Prettyprinter.Expressions
import Skeleton

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

