module UtilsSkeleton where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified Names
import qualified Skeleton

lookup_ctors :: Skeleton.Coq_skeleton -> Names.TypeName -> Prelude.Maybe
                Skeleton.Coq_ctors
lookup_ctors s tn =
  let {
   filterResult = List.filter (\x ->
                    case x of {
                     (,) n _ ->
                      Names.eq_TypeName (Datatypes.fst (Names.unscope n)) tn})
                    (Skeleton.skeleton_ctors s)}
  in
  let {
   tnresult = List.filter (Names.eq_TypeName tn) (Skeleton.skeleton_dts s)}
  in
  case tnresult of {
   [] -> Prelude.Nothing;
   (:) _ _ -> Prelude.Just filterResult}

lookup_ctor_sig :: Skeleton.Coq_skeleton -> Names.ScopedName -> Prelude.Maybe
                   Skeleton.Coq_ctor
lookup_ctor_sig s sn =
  List.find (\x -> Names.eq_ScopedName sn (Datatypes.fst x))
    (Skeleton.skeleton_ctors s)

lookup_dtors :: Skeleton.Coq_skeleton -> Names.TypeName -> Prelude.Maybe
                Skeleton.Coq_dtors
lookup_dtors ps tn =
  let {
   filterResult = List.filter (\x ->
                    case x of {
                     (,) y _ ->
                      case y of {
                       (,) n _ ->
                        Names.eq_TypeName (Datatypes.fst (Names.unscope n))
                          tn}}) (Skeleton.skeleton_dtors ps)}
  in
  let {
   tnResult = List.filter (Names.eq_TypeName tn) (Skeleton.skeleton_cdts ps)}
  in
  case tnResult of {
   [] -> Prelude.Nothing;
   (:) _ _ -> Prelude.Just filterResult}

lookup_dtor :: Skeleton.Coq_skeleton -> Names.ScopedName -> Prelude.Maybe
               Skeleton.Coq_dtor
lookup_dtor ps sn =
  List.find (\x -> Names.eq_ScopedName sn (Datatypes.fst (Datatypes.fst x)))
    (Skeleton.skeleton_dtors ps)

lookup_fun_sig :: Skeleton.Coq_skeleton -> Names.Name -> Prelude.Maybe
                  Skeleton.Coq_fun_sig
lookup_fun_sig ps n =
  List.find (\x -> Names.eq_Name n (Datatypes.fst (Datatypes.fst x)))
    (Skeleton.skeleton_fun_sigs ps)

lookup_gfun_sig_x :: Skeleton.Coq_gfun_sigs -> Names.QName -> Prelude.Maybe
                     Skeleton.Coq_gfun_sig
lookup_gfun_sig_x sigs qn =
  List.find (\sig -> Names.eq_QName qn (Datatypes.fst sig)) sigs

lookup_gfun_sig_g :: Skeleton.Coq_skeleton -> Names.QName -> Prelude.Maybe
                     Skeleton.Coq_gfun_sig
lookup_gfun_sig_g s qn =
  lookup_gfun_sig_x (Skeleton.skeleton_gfun_sigs_g s) qn

lookup_gfun_sig_l :: Skeleton.Coq_skeleton -> Names.QName -> Prelude.Maybe
                     Skeleton.Coq_gfun_sig
lookup_gfun_sig_l s qn =
  lookup_gfun_sig_x (Skeleton.skeleton_gfun_sigs_l s) qn

lookup_gfun_sig_scoped :: Skeleton.Coq_skeleton -> Names.ScopedName ->
                          Prelude.Maybe Skeleton.Coq_gfun_sig
lookup_gfun_sig_scoped s sn =
  case sn of {
   Names.Coq_local qn -> lookup_gfun_sig_l s qn;
   Names.Coq_global qn -> lookup_gfun_sig_g s qn}

lookup_cfun_sig_x :: Skeleton.Coq_cfun_sigs -> Names.QName -> Prelude.Maybe
                     Skeleton.Coq_cfun_sig
lookup_cfun_sig_x sigs qn =
  List.find (\sig -> Names.eq_QName qn (Datatypes.fst (Datatypes.fst sig)))
    sigs

lookup_cfun_sig_g :: Skeleton.Coq_skeleton -> Names.QName -> Prelude.Maybe
                     Skeleton.Coq_cfun_sig
lookup_cfun_sig_g s qn =
  lookup_cfun_sig_x (Skeleton.skeleton_cfun_sigs_g s) qn

lookup_cfun_sig_l :: Skeleton.Coq_skeleton -> Names.QName -> Prelude.Maybe
                     Skeleton.Coq_cfun_sig
lookup_cfun_sig_l s qn =
  lookup_cfun_sig_x (Skeleton.skeleton_cfun_sigs_l s) qn

lookup_cfun_sig_scoped :: Skeleton.Coq_skeleton -> Names.ScopedName ->
                          Prelude.Maybe Skeleton.Coq_cfun_sig
lookup_cfun_sig_scoped s sn =
  case sn of {
   Names.Coq_local qn -> lookup_cfun_sig_l s qn;
   Names.Coq_global qn -> lookup_cfun_sig_g s qn}

