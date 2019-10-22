module CtorizeI where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified Names
import qualified ProgramDef
import qualified Skeleton

type Constructor = (,) Names.ScopedName ([] Names.TypeName)

computeNewDatatype :: ProgramDef.Coq_program -> Names.TypeName -> []
                      Constructor
computeNewDatatype p n =
  Datatypes.app
    (List.map (\x -> (,) (Names.Coq_global (Datatypes.fst x))
      (Datatypes.snd x))
      (List.filter (\x ->
        Names.eq_TypeName (Datatypes.fst (Datatypes.fst x)) n)
        (Skeleton.skeleton_gfun_sigs_g (ProgramDef.program_skeleton p))))
    (List.map (\x -> (,) (Names.Coq_local (Datatypes.fst x))
      (Datatypes.snd x))
      (List.filter (\x ->
        Names.eq_TypeName (Datatypes.fst (Datatypes.fst x)) n)
        (Skeleton.skeleton_gfun_sigs_l (ProgramDef.program_skeleton p))))

new_cdts :: ProgramDef.Coq_program -> Names.TypeName -> [] Names.TypeName
new_cdts p n =
  List.filter (\n' -> Datatypes.negb (Names.eq_TypeName n n'))
    (Skeleton.skeleton_cdts (ProgramDef.program_skeleton p))

new_dtors :: ProgramDef.Coq_program -> Names.TypeName -> []
             ((,) ((,) Names.ScopedName ([] Names.TypeName)) Names.TypeName)
new_dtors p n =
  List.filter (\x ->
    case x of {
     (,) y _ ->
      case y of {
       (,) n' _ ->
        Datatypes.negb
          (Names.eq_TypeName n (Datatypes.fst (Names.unscope n')))}})
    (Skeleton.skeleton_dtors (ProgramDef.program_skeleton p))

cfunsigs_mapfun :: ((,) ((,) Names.ScopedName ([] Names.TypeName))
                   Names.TypeName) -> (,)
                   ((,) Names.QName ([] Names.TypeName)) Names.TypeName
cfunsigs_mapfun x =
  case x of {
   (,) p x3 -> case p of {
                (,) x1 x2 -> (,) ((,) (Names.unscope x1) x2) x3}}

cfunsigs_filterfun_g :: Names.TypeName -> ((,)
                        ((,) Names.ScopedName ([] Names.TypeName))
                        Names.TypeName) -> Prelude.Bool
cfunsigs_filterfun_g n x =
  case x of {
   (,) p _ ->
    case p of {
     (,) s _ ->
      case s of {
       Names.Coq_local _ -> Prelude.False;
       Names.Coq_global n' -> Names.eq_TypeName n (Datatypes.fst n')}}}

new_cfunsigs_g :: ProgramDef.Coq_program -> Names.TypeName -> []
                  ((,) ((,) Names.QName ([] Names.TypeName)) Names.TypeName)
new_cfunsigs_g p n =
  Datatypes.app
    (List.map cfunsigs_mapfun
      (List.filter (cfunsigs_filterfun_g n)
        (Skeleton.skeleton_dtors (ProgramDef.program_skeleton p))))
    (Skeleton.skeleton_cfun_sigs_g (ProgramDef.program_skeleton p))

cfunsigs_filterfun_l :: Names.TypeName -> ((,)
                        ((,) Names.ScopedName ([] Names.TypeName))
                        Names.TypeName) -> Prelude.Bool
cfunsigs_filterfun_l n x =
  case x of {
   (,) p _ ->
    case p of {
     (,) s _ ->
      case s of {
       Names.Coq_local n' -> Names.eq_TypeName n (Datatypes.fst n');
       Names.Coq_global _ -> Prelude.False}}}

new_cfunsigs_l :: ProgramDef.Coq_program -> Names.TypeName -> []
                  ((,) ((,) Names.QName ([] Names.TypeName)) Names.TypeName)
new_cfunsigs_l p n =
  Datatypes.app
    (List.map cfunsigs_mapfun
      (List.filter (cfunsigs_filterfun_l n)
        (Skeleton.skeleton_dtors (ProgramDef.program_skeleton p))))
    (Skeleton.skeleton_cfun_sigs_l (ProgramDef.program_skeleton p))

new_gfunsigs_g :: ProgramDef.Coq_program -> Names.TypeName -> []
                  ((,) ((,) Names.TypeName Names.Name) ([] Names.TypeName))
new_gfunsigs_g p n =
  List.filter (\x ->
    case x of {
     (,) n' _ -> Datatypes.negb (Names.eq_TypeName n (Datatypes.fst n'))})
    (Skeleton.skeleton_gfun_sigs_g (ProgramDef.program_skeleton p))

new_gfunsigs_l :: ProgramDef.Coq_program -> Names.TypeName -> []
                  ((,) ((,) Names.TypeName Names.Name) ([] Names.TypeName))
new_gfunsigs_l p n =
  List.filter (\x ->
    case x of {
     (,) n' _ -> Datatypes.negb (Names.eq_TypeName n (Datatypes.fst n'))})
    (Skeleton.skeleton_gfun_sigs_l (ProgramDef.program_skeleton p))

constructorize_to_skeleton :: ProgramDef.Coq_program -> Names.TypeName ->
                              Skeleton.Coq_skeleton
constructorize_to_skeleton p n =
  let {newDatatype = computeNewDatatype p n} in
  Skeleton.Coq_mkSkeleton ((:) n
  (Skeleton.skeleton_dts (ProgramDef.program_skeleton p)))
  (Datatypes.app newDatatype
    (Skeleton.skeleton_ctors (ProgramDef.program_skeleton p))) (new_cdts p n)
  (new_dtors p n)
  (Skeleton.skeleton_fun_sigs (ProgramDef.program_skeleton p))
  (new_cfunsigs_g p n) (new_cfunsigs_l p n) (new_gfunsigs_g p n)
  (new_gfunsigs_l p n)

