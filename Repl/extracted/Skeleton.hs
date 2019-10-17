module Skeleton where

import qualified Prelude
import qualified Names

type Coq_dts = [] Names.TypeName

type Coq_ctor = (,) Names.ScopedName ([] Names.TypeName)

type Coq_ctors = [] Coq_ctor

type Coq_cdts = [] Names.TypeName

type Coq_dtor = (,) ((,) Names.ScopedName ([] Names.TypeName)) Names.TypeName

type Coq_dtors = [] Coq_dtor

type Coq_fun_sig = (,) ((,) Names.Name ([] Names.TypeName)) Names.TypeName

type Coq_fun_sigs = [] Coq_fun_sig

type Coq_cfun_sig = (,) ((,) Names.QName ([] Names.TypeName)) Names.TypeName

type Coq_cfun_sigs = [] Coq_cfun_sig

type Coq_gfun_sig = (,) Names.QName ([] Names.TypeName)

type Coq_gfun_sigs = [] Coq_gfun_sig

data Coq_skeleton =
   Coq_mkSkeleton Coq_dts Coq_ctors Coq_cdts Coq_dtors Coq_fun_sigs Coq_cfun_sigs 
 Coq_cfun_sigs Coq_gfun_sigs Coq_gfun_sigs

skeleton_dts :: Coq_skeleton -> Coq_dts
skeleton_dts s =
  case s of {
   Coq_mkSkeleton skeleton_dts0 _ _ _ _ _ _ _ _ -> skeleton_dts0}

skeleton_ctors :: Coq_skeleton -> Coq_ctors
skeleton_ctors s =
  case s of {
   Coq_mkSkeleton _ skeleton_ctors0 _ _ _ _ _ _ _ -> skeleton_ctors0}

skeleton_cdts :: Coq_skeleton -> Coq_cdts
skeleton_cdts s =
  case s of {
   Coq_mkSkeleton _ _ skeleton_cdts0 _ _ _ _ _ _ -> skeleton_cdts0}

skeleton_dtors :: Coq_skeleton -> Coq_dtors
skeleton_dtors s =
  case s of {
   Coq_mkSkeleton _ _ _ skeleton_dtors0 _ _ _ _ _ -> skeleton_dtors0}

skeleton_fun_sigs :: Coq_skeleton -> Coq_fun_sigs
skeleton_fun_sigs s =
  case s of {
   Coq_mkSkeleton _ _ _ _ skeleton_fun_sigs0 _ _ _ _ -> skeleton_fun_sigs0}

skeleton_cfun_sigs_g :: Coq_skeleton -> Coq_cfun_sigs
skeleton_cfun_sigs_g s =
  case s of {
   Coq_mkSkeleton _ _ _ _ _ skeleton_cfun_sigs_g0 _ _ _ ->
    skeleton_cfun_sigs_g0}

skeleton_cfun_sigs_l :: Coq_skeleton -> Coq_cfun_sigs
skeleton_cfun_sigs_l s =
  case s of {
   Coq_mkSkeleton _ _ _ _ _ _ skeleton_cfun_sigs_l0 _ _ ->
    skeleton_cfun_sigs_l0}

skeleton_gfun_sigs_g :: Coq_skeleton -> Coq_gfun_sigs
skeleton_gfun_sigs_g s =
  case s of {
   Coq_mkSkeleton _ _ _ _ _ _ _ skeleton_gfun_sigs_g0 _ ->
    skeleton_gfun_sigs_g0}

skeleton_gfun_sigs_l :: Coq_skeleton -> Coq_gfun_sigs
skeleton_gfun_sigs_l s =
  case s of {
   Coq_mkSkeleton _ _ _ _ _ _ _ _ skeleton_gfun_sigs_l0 ->
    skeleton_gfun_sigs_l0}

emptySkeleton :: Coq_skeleton
emptySkeleton =
  Coq_mkSkeleton [] [] [] [] [] [] [] [] []

