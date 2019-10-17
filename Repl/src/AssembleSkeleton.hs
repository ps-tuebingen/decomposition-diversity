module AssembleSkeleton
  (
    assembleSkeleton
  ) where

import Names (TypeName, ScopedName, QName, Name)
import Skeleton
import Parser.ParserDefinition (TypeNameParse(..), FNameParse(..), VarNameParse(..))
import Parser.Declarations (Declaration(..))

type DataType = (TypeName,[(ScopedName, [TypeName])])
type CoDataType = (TypeName,[((ScopedName, [TypeName]),TypeName)])

-- | Add a datatype to a Coq_skeleton.
addDtToSkeleton :: DataType -> Coq_skeleton -> Coq_skeleton
addDtToSkeleton (tn, ctors') (Coq_mkSkeleton dts ctors cdts dtors fun_sigs cfun_sigs_g cfun_sigs_l gfun_sigs_g gfun_sigs_l) =
  (Coq_mkSkeleton (tn : dts) (ctors' ++ ctors) cdts dtors fun_sigs cfun_sigs_g cfun_sigs_l gfun_sigs_g gfun_sigs_l)

-- | Add a codatatype to a Coq_skeleton.
addCdtToSkeleton :: CoDataType -> Coq_skeleton -> Coq_skeleton
addCdtToSkeleton (tn, dtors') (Coq_mkSkeleton dts ctors cdts dtors fun_sigs cfun_sigs_g cfun_sigs_l gfun_sigs_g gfun_sigs_l) =
  (Coq_mkSkeleton dts ctors (tn : cdts) (dtors' ++ dtors) fun_sigs cfun_sigs_g cfun_sigs_l gfun_sigs_g gfun_sigs_l)

type FunSig = ((Name, [TypeName]), TypeName)

-- | Add function signature to program skeleton.
addFunSigToSkeleton :: FunSig -> Coq_skeleton -> Coq_skeleton
addFunSigToSkeleton fs (Coq_mkSkeleton dts ctors cdts dtors fun_sigs cfun_sigs_g cfun_sigs_l gfun_sigs_g gfun_sigs_l) =
  Coq_mkSkeleton dts ctors cdts dtors (fs : fun_sigs) cfun_sigs_g cfun_sigs_l gfun_sigs_g gfun_sigs_l

type GenFunSig = (QName, [TypeName]) --  Coq_comatchfunctionsigtable

-- | Add generator function signature to program skeleton.
addGenFunSigToSkeleton :: GenFunSig -> Coq_skeleton -> Coq_skeleton
addGenFunSigToSkeleton gfsig (Coq_mkSkeleton dts ctors cdts dtors fun_sigs cfun_sigs_g cfun_sigs_l gfun_sigs_g gfun_sigs_l) =
  Coq_mkSkeleton dts ctors cdts dtors fun_sigs cfun_sigs_g cfun_sigs_l (gfsig : gfun_sigs_g) gfun_sigs_l 

type ConFunSig = ((QName, [TypeName]), TypeName) --  Coq_matchfunctionsigtable

-- | Add consumer function signature to program skeleton.
addConFunSigToSkeleton :: ConFunSig -> Coq_skeleton -> Coq_skeleton
addConFunSigToSkeleton cfsig (Coq_mkSkeleton dts ctors cdts dtors fun_sigs cfun_sigs_g cfun_sigs_l gfun_sigs_g gfun_sigs_l) =
  Coq_mkSkeleton dts ctors cdts dtors fun_sigs (cfsig : cfun_sigs_g) cfun_sigs_l gfun_sigs_g gfun_sigs_l

-- | Add a single declaration to an already existing program skeleton.
addDeclarationToSkeleton :: Declaration -> Coq_skeleton -> Coq_skeleton
addDeclarationToSkeleton (DataTypeD (TypeNameParse tn) ctors)    sk =
  addDtToSkeleton        (tn,parsedCtors2ctors ctors)  sk
addDeclarationToSkeleton (CoDataTypeD (TypeNameParse tn) dtors) sk  =
  addCdtToSkeleton       (tn, parsedDtors2dtors dtors) sk
addDeclarationToSkeleton (FunctionD (FNameParse fname) fargs (TypeNameParse rtype) _) sk =
  addFunSigToSkeleton ((fname, unmapTypeNameParse <$> fargs), rtype) sk
addDeclarationToSkeleton (GenFunD   qn fargs _) sk =
  addGenFunSigToSkeleton (qn, unmapTypeNameParse <$> fargs) sk
addDeclarationToSkeleton (ConFunD   qn fargs (TypeNameParse rtype) _) sk =
  addConFunSigToSkeleton ((qn, unmapTypeNameParse <$> fargs), rtype) sk

-- | Generate a Skeleton from a list of declarations.
assembleSkeleton :: [Declaration] -> Coq_skeleton
assembleSkeleton = foldr addDeclarationToSkeleton emptySkeleton

parsedCtors2ctors :: [(ScopedName, [TypeNameParse])] -> [(ScopedName, [TypeName])]
parsedCtors2ctors ctors_parsed = (\(sn, targs) -> (sn, (\(TypeNameParse tn) -> tn) <$> targs)) <$> ctors_parsed

parsedDtors2dtors :: [(ScopedName, [TypeNameParse], TypeNameParse)] -> [((ScopedName, [TypeName]), TypeName)]
parsedDtors2dtors ctors_parsed = (\(sn, targs, TypeNameParse rtype) -> ((sn, (\(TypeNameParse tn) -> tn) <$> targs), rtype)) <$> ctors_parsed

unmapTypeNameParse :: (VarNameParse, TypeNameParse) -> TypeName
unmapTypeNameParse (_, TypeNameParse tn) = tn

