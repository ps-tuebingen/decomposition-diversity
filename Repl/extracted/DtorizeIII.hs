module DtorizeIII where

import qualified Prelude
import qualified AST
import qualified BodyTypeDefs
import qualified Datatypes
import qualified DtorizeI
import qualified DtorizeII
import qualified List
import qualified Names
import qualified ProgramDef
import qualified Skeleton
import qualified Specif
import qualified SwitchIndices

new_fun_bods :: ProgramDef.Coq_program -> Names.TypeName ->
                BodyTypeDefs.Coq_fun_bods
new_fun_bods p tn =
  List.map (\x -> (,) (Datatypes.fst x)
    (DtorizeII.destructorize_expr tn (Datatypes.snd x)))
    (ProgramDef.program_fun_bods p)

new_cfun_bods_g :: ProgramDef.Coq_program -> Names.TypeName ->
                   BodyTypeDefs.Coq_cfun_bods
new_cfun_bods_g p tn =
  List.filter (\x ->
    case x of {
     (,) n' _ -> Datatypes.negb (Names.eq_TypeName tn (Datatypes.fst n'))})
    (List.map (\x -> (,) (Datatypes.fst x)
      (List.map (\y -> (,) (Datatypes.fst y)
        (DtorizeII.destructorize_expr tn (Datatypes.snd y)))
        (Datatypes.snd x))) (ProgramDef.program_cfun_bods_g p))

new_cfun_bods_l :: ProgramDef.Coq_program -> Names.TypeName ->
                   BodyTypeDefs.Coq_cfun_bods
new_cfun_bods_l p tn =
  List.filter (\x ->
    case x of {
     (,) n' _ -> Datatypes.negb (Names.eq_TypeName tn (Datatypes.fst n'))})
    (List.map (\x -> (,) (Datatypes.fst x)
      (List.map (\y -> (,) (Datatypes.fst y)
        (DtorizeII.destructorize_expr tn (Datatypes.snd y)))
        (Datatypes.snd x))) (ProgramDef.program_cfun_bods_l p))

gfunbods_filterfun_g :: Names.QName -> ((,) Names.QName
                        ((,) Names.ScopedName AST.Coq_expr)) -> Prelude.Bool
gfunbods_filterfun_g q x =
  case x of {
   (,) q0 p ->
    case q0 of {
     (,) tn _ ->
      case p of {
       (,) s _ ->
        case s of {
         Names.Coq_local _ -> Prelude.False;
         Names.Coq_global q' ->
          Datatypes.andb (Names.eq_TypeName tn (Datatypes.fst q))
            (Names.eq_QName q q')}}}}

switch_indices_aux :: Skeleton.Coq_skeleton -> Names.ScopedName ->
                      Prelude.Integer -> Names.TypeName -> AST.Coq_expr ->
                      AST.Coq_expr
switch_indices_aux p sn n tn e =
  DtorizeII.destructorize_expr tn
    (Specif.proj1_sig (SwitchIndices.switch_indices_cfun e p sn n))

globalize_aux :: ([] ((,) Names.QName a1)) -> [] ((,) Names.ScopedName a1)
globalize_aux =
  List.map (\x -> (,) (Names.Coq_global (Datatypes.fst x)) (Datatypes.snd x))

localize_aux :: ([] ((,) Names.QName a1)) -> [] ((,) Names.ScopedName a1)
localize_aux =
  List.map (\x -> (,) (Names.Coq_local (Datatypes.fst x)) (Datatypes.snd x))

new_gfun_bods_g :: ProgramDef.Coq_program -> Names.TypeName ->
                   BodyTypeDefs.Coq_gfun_bods
new_gfun_bods_g p tn =
  Datatypes.app
    (List.map (\ctor -> (,) (Names.unscope (Datatypes.fst ctor))
      (Datatypes.app
        (List.map (\x -> (,) (Datatypes.fst x)
          (switch_indices_aux (ProgramDef.program_skeleton p)
            (Datatypes.fst x) (Datatypes.length (Datatypes.snd ctor)) tn
            (Datatypes.snd (Datatypes.snd x))))
          (globalize_aux
            (List.filter
              (gfunbods_filterfun_g (Names.unscope (Datatypes.fst ctor)))
              (List.flat_map (\x ->
                List.map (\y -> (,) (Datatypes.fst x) y) (Datatypes.snd x))
                (ProgramDef.program_cfun_bods_g p)))))
        (List.map (\x -> (,) (Datatypes.fst x)
          (switch_indices_aux (ProgramDef.program_skeleton p)
            (Datatypes.fst x) (Datatypes.length (Datatypes.snd ctor)) tn
            (Datatypes.snd (Datatypes.snd x))))
          (localize_aux
            (List.filter
              (gfunbods_filterfun_g (Names.unscope (Datatypes.fst ctor)))
              (List.flat_map (\x ->
                List.map (\y -> (,) (Datatypes.fst x) y) (Datatypes.snd x))
                (ProgramDef.program_cfun_bods_l p)))))))
      (List.filter (DtorizeI.gfunsigs_filterfun_g tn)
        (Skeleton.skeleton_ctors (ProgramDef.program_skeleton p))))
    (List.map (\x -> (,) (Datatypes.fst x)
      (List.map (\y -> (,) (Datatypes.fst y)
        (DtorizeII.destructorize_expr tn (Datatypes.snd y)))
        (Datatypes.snd x))) (ProgramDef.program_gfun_bods_g p))

gfunbods_filterfun_l :: Names.QName -> ((,) Names.QName
                        ((,) Names.ScopedName AST.Coq_expr)) -> Prelude.Bool
gfunbods_filterfun_l q x =
  case x of {
   (,) q0 p ->
    case q0 of {
     (,) tn _ ->
      case p of {
       (,) s _ ->
        case s of {
         Names.Coq_local q' ->
          Datatypes.andb (Names.eq_TypeName tn (Datatypes.fst q))
            (Names.eq_QName q q');
         Names.Coq_global _ -> Prelude.False}}}}

new_gfun_bods_l :: ProgramDef.Coq_program -> Names.TypeName ->
                   BodyTypeDefs.Coq_gfun_bods
new_gfun_bods_l p tn =
  Datatypes.app
    (List.map (\ctor -> (,) (Names.unscope (Datatypes.fst ctor))
      (Datatypes.app
        (List.map (\x -> (,) (Datatypes.fst x)
          (switch_indices_aux (ProgramDef.program_skeleton p)
            (Datatypes.fst x) (Datatypes.length (Datatypes.snd ctor)) tn
            (Datatypes.snd (Datatypes.snd x))))
          (globalize_aux
            (List.filter
              (gfunbods_filterfun_l (Names.unscope (Datatypes.fst ctor)))
              (List.flat_map (\x ->
                List.map (\y -> (,) (Datatypes.fst x) y) (Datatypes.snd x))
                (ProgramDef.program_cfun_bods_g p)))))
        (List.map (\x -> (,) (Datatypes.fst x)
          (switch_indices_aux (ProgramDef.program_skeleton p)
            (Datatypes.fst x) (Datatypes.length (Datatypes.snd ctor)) tn
            (Datatypes.snd (Datatypes.snd x))))
          (localize_aux
            (List.filter
              (gfunbods_filterfun_l (Names.unscope (Datatypes.fst ctor)))
              (List.flat_map (\x ->
                List.map (\y -> (,) (Datatypes.fst x) y) (Datatypes.snd x))
                (ProgramDef.program_cfun_bods_l p)))))))
      (List.filter (DtorizeI.gfunsigs_filterfun_l tn)
        (Skeleton.skeleton_ctors (ProgramDef.program_skeleton p))))
    (List.map (\x -> (,) (Datatypes.fst x)
      (List.map (\y -> (,) (Datatypes.fst y)
        (DtorizeII.destructorize_expr tn (Datatypes.snd y)))
        (Datatypes.snd x))) (ProgramDef.program_gfun_bods_l p))

destructorize_program :: ProgramDef.Coq_program -> Names.TypeName ->
                         ProgramDef.Coq_program
destructorize_program p tn =
  ProgramDef.Coq_mkProgram (DtorizeI.destructorize_to_skeleton p tn)
    (new_fun_bods p tn) (new_cfun_bods_g p tn) (new_cfun_bods_l p tn)
    (new_gfun_bods_g p tn) (new_gfun_bods_l p tn)

