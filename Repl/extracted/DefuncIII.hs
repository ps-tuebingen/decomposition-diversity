module DefuncIII where

import qualified Prelude
import qualified AST
import qualified BodyTypeDefs
import qualified Datatypes
import qualified DefuncI
import qualified DefuncII
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
    (DefuncII.defunctionalize_expr tn (Datatypes.snd x)))
    (ProgramDef.program_fun_bods p)

cfunbods_filterfun_g :: Names.QName -> ((,) Names.QName
                        ((,) Names.ScopedName AST.Coq_expr)) -> Prelude.Bool
cfunbods_filterfun_g q x =
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
  DefuncII.defunctionalize_expr tn
    (Specif.proj1_sig (SwitchIndices.switch_indices e p sn n))

globalize_aux :: ([] ((,) Names.QName a1)) -> [] ((,) Names.ScopedName a1)
globalize_aux =
  List.map (\x -> (,) (Names.Coq_global (Datatypes.fst x)) (Datatypes.snd x))

localize_aux :: ([] ((,) Names.QName a1)) -> [] ((,) Names.ScopedName a1)
localize_aux =
  List.map (\x -> (,) (Names.Coq_local (Datatypes.fst x)) (Datatypes.snd x))

new_cfun_bods_g :: ProgramDef.Coq_program -> Names.TypeName ->
                   BodyTypeDefs.Coq_cfun_bods
new_cfun_bods_g p tn =
  Datatypes.app
    (List.map (\dtor -> (,)
      (Names.unscope (Datatypes.fst (Datatypes.fst dtor)))
      (Datatypes.app
        (List.map (\x -> (,) (Datatypes.fst x)
          (switch_indices_aux (ProgramDef.program_skeleton p)
            (Datatypes.fst x)
            (Datatypes.length (Datatypes.snd (Datatypes.fst dtor))) tn
            (Datatypes.snd (Datatypes.snd x))))
          (globalize_aux
            (List.filter
              (cfunbods_filterfun_g
                (Names.unscope (Datatypes.fst (Datatypes.fst dtor))))
              (List.flat_map (\x ->
                List.map (\y -> (,) (Datatypes.fst x) y) (Datatypes.snd x))
                (ProgramDef.program_gfun_bods_g p)))))
        (List.map (\x -> (,) (Datatypes.fst x)
          (switch_indices_aux (ProgramDef.program_skeleton p)
            (Datatypes.fst x)
            (Datatypes.length (Datatypes.snd (Datatypes.fst dtor))) tn
            (Datatypes.snd (Datatypes.snd x))))
          (localize_aux
            (List.filter
              (cfunbods_filterfun_g
                (Names.unscope (Datatypes.fst (Datatypes.fst dtor))))
              (List.flat_map (\x ->
                List.map (\y -> (,) (Datatypes.fst x) y) (Datatypes.snd x))
                (ProgramDef.program_gfun_bods_l p)))))))
      (List.filter (DefuncI.cfunsigs_filterfun_g tn)
        (Skeleton.skeleton_dtors (ProgramDef.program_skeleton p))))
    (List.map (\x -> (,) (Datatypes.fst x)
      (List.map (\y -> (,) (Datatypes.fst y)
        (DefuncII.defunctionalize_expr tn (Datatypes.snd y)))
        (Datatypes.snd x))) (ProgramDef.program_cfun_bods_g p))

cfunbods_filterfun_l :: Names.QName -> ((,) Names.QName
                        ((,) Names.ScopedName AST.Coq_expr)) -> Prelude.Bool
cfunbods_filterfun_l q x =
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

new_cfun_bods_l :: ProgramDef.Coq_program -> Names.TypeName ->
                   BodyTypeDefs.Coq_cfun_bods
new_cfun_bods_l p tn =
  Datatypes.app
    (List.map (\dtor -> (,)
      (Names.unscope (Datatypes.fst (Datatypes.fst dtor)))
      (Datatypes.app
        (List.map (\x -> (,) (Datatypes.fst x)
          (switch_indices_aux (ProgramDef.program_skeleton p)
            (Datatypes.fst x)
            (Datatypes.length (Datatypes.snd (Datatypes.fst dtor))) tn
            (Datatypes.snd (Datatypes.snd x))))
          (globalize_aux
            (List.filter
              (cfunbods_filterfun_l
                (Names.unscope (Datatypes.fst (Datatypes.fst dtor))))
              (List.flat_map (\x ->
                List.map (\y -> (,) (Datatypes.fst x) y) (Datatypes.snd x))
                (ProgramDef.program_gfun_bods_g p)))))
        (List.map (\x -> (,) (Datatypes.fst x)
          (switch_indices_aux (ProgramDef.program_skeleton p)
            (Datatypes.fst x)
            (Datatypes.length (Datatypes.snd (Datatypes.fst dtor))) tn
            (Datatypes.snd (Datatypes.snd x))))
          (localize_aux
            (List.filter
              (cfunbods_filterfun_l
                (Names.unscope (Datatypes.fst (Datatypes.fst dtor))))
              (List.flat_map (\x ->
                List.map (\y -> (,) (Datatypes.fst x) y) (Datatypes.snd x))
                (ProgramDef.program_gfun_bods_l p)))))))
      (List.filter (DefuncI.cfunsigs_filterfun_l tn)
        (Skeleton.skeleton_dtors (ProgramDef.program_skeleton p))))
    (List.map (\x -> (,) (Datatypes.fst x)
      (List.map (\y -> (,) (Datatypes.fst y)
        (DefuncII.defunctionalize_expr tn (Datatypes.snd y)))
        (Datatypes.snd x))) (ProgramDef.program_cfun_bods_l p))

new_gfun_bods_g :: ProgramDef.Coq_program -> Names.TypeName ->
                   BodyTypeDefs.Coq_cfun_bods
new_gfun_bods_g p tn =
  List.filter (\x ->
    case x of {
     (,) n' _ -> Datatypes.negb (Names.eq_TypeName tn (Datatypes.fst n'))})
    (List.map (\x -> (,) (Datatypes.fst x)
      (List.map (\y -> (,) (Datatypes.fst y)
        (DefuncII.defunctionalize_expr tn (Datatypes.snd y)))
        (Datatypes.snd x))) (ProgramDef.program_gfun_bods_g p))

new_gfun_bods_l :: ProgramDef.Coq_program -> Names.TypeName ->
                   BodyTypeDefs.Coq_cfun_bods
new_gfun_bods_l p tn =
  List.filter (\x ->
    case x of {
     (,) n' _ -> Datatypes.negb (Names.eq_TypeName tn (Datatypes.fst n'))})
    (List.map (\x -> (,) (Datatypes.fst x)
      (List.map (\y -> (,) (Datatypes.fst y)
        (DefuncII.defunctionalize_expr tn (Datatypes.snd y)))
        (Datatypes.snd x))) (ProgramDef.program_gfun_bods_l p))

defunctionalize_program :: ProgramDef.Coq_program -> Names.TypeName ->
                           ProgramDef.Coq_program
defunctionalize_program p tn =
  ProgramDef.Coq_mkProgram (DefuncI.defunctionalize_to_skeleton p tn)
    (new_fun_bods p tn) (new_cfun_bods_g p tn) (new_cfun_bods_l p tn)
    (new_gfun_bods_g p tn) (new_gfun_bods_l p tn)

