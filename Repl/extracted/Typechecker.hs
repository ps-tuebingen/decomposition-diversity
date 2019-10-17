module Typechecker where

import qualified Prelude
import qualified AST
import qualified Datatypes
import qualified List
import qualified Names
import qualified PeanoNat
import qualified Skeleton
import qualified SumMonad
import qualified UtilsSkeleton

type Coq_error = Datatypes.Coq_unit

dummy :: Datatypes.Coq_sum Coq_error a1
dummy =
  Datatypes.Coq_inl Datatypes.Coq_tt

nth_sum :: Prelude.Integer -> ([] a1) -> Datatypes.Coq_sum Coq_error a1
nth_sum n ls =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> case ls of {
            [] -> dummy;
            (:) x _ -> Datatypes.Coq_inr x})
    (\n0 -> case ls of {
             [] -> dummy;
             (:) _ xs -> nth_sum n0 xs})
    n

wrap_sum :: (Prelude.Maybe a1) -> Datatypes.Coq_sum Coq_error a1
wrap_sum x =
  case x of {
   Prelude.Just y -> Datatypes.Coq_inr y;
   Prelude.Nothing -> dummy}

type Coq_ctxt = [] Names.TypeName

typecheck :: Skeleton.Coq_skeleton -> Coq_ctxt -> AST.Coq_expr ->
             Datatypes.Coq_sum Coq_error Names.TypeName
typecheck ps ctx e =
  let {
   typecheck_eq = \p ctx0 e0 t ->
    case typecheck p ctx0 e0 of {
     Datatypes.Coq_inl _ -> Prelude.False;
     Datatypes.Coq_inr t' -> Names.eq_TypeName t t'}}
  in
  case e of {
   AST.E_Var v -> nth_sum v ctx;
   AST.E_Constr sn args ->
    SumMonad.bind_sum (wrap_sum (UtilsSkeleton.lookup_ctor_sig ps sn))
      (\ctor ->
      case Datatypes.andb
             (PeanoNat._Nat__eqb (Datatypes.length (Datatypes.snd ctor))
               (Datatypes.length args))
             (List.forallb (\x ->
               case x of {
                (,) t1 y ->
                 case y of {
                  Datatypes.Coq_inl _ -> Prelude.False;
                  Datatypes.Coq_inr t2 -> Names.eq_TypeName t1 t2}})
               (List.combine (Datatypes.snd ctor)
                 (List.map (typecheck ps ctx) args))) of {
       Prelude.True -> Datatypes.Coq_inr (Datatypes.fst (Names.unscope sn));
       Prelude.False -> dummy});
   AST.E_DestrCall sn ex args ->
    SumMonad.bind_sum (wrap_sum (UtilsSkeleton.lookup_dtor ps sn)) (\dtor ->
      case Datatypes.andb
             (PeanoNat._Nat__eqb
               (Datatypes.length (Datatypes.snd (Datatypes.fst dtor)))
               (Datatypes.length args))
             (Datatypes.andb
               (typecheck_eq ps ctx ex (Datatypes.fst (Names.unscope sn)))
               (List.forallb (\x ->
                 case x of {
                  (,) t1 y ->
                   case y of {
                    Datatypes.Coq_inl _ -> Prelude.False;
                    Datatypes.Coq_inr t2 -> Names.eq_TypeName t1 t2}})
                 (List.combine (Datatypes.snd (Datatypes.fst dtor))
                   (List.map (typecheck ps ctx) args)))) of {
       Prelude.True -> Datatypes.Coq_inr (Datatypes.snd dtor);
       Prelude.False -> dummy});
   AST.E_FunCall n args ->
    SumMonad.bind_sum (wrap_sum (UtilsSkeleton.lookup_fun_sig ps n))
      (\fsig ->
      case Datatypes.andb
             (PeanoNat._Nat__eqb
               (Datatypes.length (Datatypes.snd (Datatypes.fst fsig)))
               (Datatypes.length args))
             (List.forallb (\x ->
               case x of {
                (,) t1 y ->
                 case y of {
                  Datatypes.Coq_inl _ -> Prelude.False;
                  Datatypes.Coq_inr t2 -> Names.eq_TypeName t1 t2}})
               (List.combine (Datatypes.snd (Datatypes.fst fsig))
                 (List.map (typecheck ps ctx) args))) of {
       Prelude.True -> Datatypes.Coq_inr (Datatypes.snd fsig);
       Prelude.False -> dummy});
   AST.E_GenFunCall s args ->
    case s of {
     Names.Coq_local qn ->
      SumMonad.bind_sum (wrap_sum (UtilsSkeleton.lookup_gfun_sig_l ps qn))
        (\gfsig ->
        case Datatypes.andb
               (PeanoNat._Nat__eqb (Datatypes.length (Datatypes.snd gfsig))
                 (Datatypes.length args))
               (List.forallb (\x ->
                 case x of {
                  (,) t1 y ->
                   case y of {
                    Datatypes.Coq_inl _ -> Prelude.False;
                    Datatypes.Coq_inr t2 -> Names.eq_TypeName t1 t2}})
                 (List.combine (Datatypes.snd gfsig)
                   (List.map (typecheck ps ctx) args))) of {
         Prelude.True -> Datatypes.Coq_inr (Datatypes.fst qn);
         Prelude.False -> dummy});
     Names.Coq_global qn ->
      SumMonad.bind_sum (wrap_sum (UtilsSkeleton.lookup_gfun_sig_g ps qn))
        (\gfsig ->
        case Datatypes.andb
               (PeanoNat._Nat__eqb (Datatypes.length (Datatypes.snd gfsig))
                 (Datatypes.length args))
               (List.forallb (\x ->
                 case x of {
                  (,) t1 y ->
                   case y of {
                    Datatypes.Coq_inl _ -> Prelude.False;
                    Datatypes.Coq_inr t2 -> Names.eq_TypeName t1 t2}})
                 (List.combine (Datatypes.snd gfsig)
                   (List.map (typecheck ps ctx) args))) of {
         Prelude.True -> Datatypes.Coq_inr (Datatypes.fst qn);
         Prelude.False -> dummy})};
   AST.E_ConsFunCall s ex args ->
    case s of {
     Names.Coq_local qn ->
      SumMonad.bind_sum (wrap_sum (UtilsSkeleton.lookup_cfun_sig_l ps qn))
        (\cfsig ->
        case Datatypes.andb (typecheck_eq ps ctx ex (Datatypes.fst qn))
               (Datatypes.andb
                 (PeanoNat._Nat__eqb
                   (Datatypes.length (Datatypes.snd (Datatypes.fst cfsig)))
                   (Datatypes.length args))
                 (List.forallb (\x ->
                   case x of {
                    (,) t1 y ->
                     case y of {
                      Datatypes.Coq_inl _ -> Prelude.False;
                      Datatypes.Coq_inr t2 -> Names.eq_TypeName t1 t2}})
                   (List.combine (Datatypes.snd (Datatypes.fst cfsig))
                     (List.map (typecheck ps ctx) args)))) of {
         Prelude.True -> Datatypes.Coq_inr (Datatypes.snd cfsig);
         Prelude.False -> dummy});
     Names.Coq_global qn ->
      SumMonad.bind_sum (wrap_sum (UtilsSkeleton.lookup_cfun_sig_g ps qn))
        (\cfsig ->
        case Datatypes.andb (typecheck_eq ps ctx ex (Datatypes.fst qn))
               (Datatypes.andb
                 (PeanoNat._Nat__eqb
                   (Datatypes.length (Datatypes.snd (Datatypes.fst cfsig)))
                   (Datatypes.length args))
                 (List.forallb (\x ->
                   case x of {
                    (,) t1 y ->
                     case y of {
                      Datatypes.Coq_inl _ -> Prelude.False;
                      Datatypes.Coq_inr t2 -> Names.eq_TypeName t1 t2}})
                   (List.combine (Datatypes.snd (Datatypes.fst cfsig))
                     (List.map (typecheck ps ctx) args)))) of {
         Prelude.True -> Datatypes.Coq_inr (Datatypes.snd cfsig);
         Prelude.False -> dummy})};
   AST.E_Match qn ex bs cases rtype ->
    let {bs_types = List.map Datatypes.snd bs} in
    let {
     bs_check = List.forallb (\x ->
                  typecheck_eq ps ctx (Datatypes.fst x) (Datatypes.snd x)) bs}
    in
    let {ctors = UtilsSkeleton.lookup_ctors ps (Datatypes.fst qn)} in
    let {
     typecheck_cases = let {
                        typecheck_cases ps0 ctxs cases0 rtype0 bs_types0 ctors0 =
                          case ctxs of {
                           [] ->
                            case cases0 of {
                             [] ->
                              case ctors0 of {
                               [] -> Prelude.True;
                               (:) _ _ -> Prelude.False};
                             (:) _ _ -> Prelude.False};
                           (:) ctx0 ctxs0 ->
                            case cases0 of {
                             [] -> Prelude.False;
                             (:) p cases' ->
                              case p of {
                               (,) name body ->
                                case ctors0 of {
                                 [] -> Prelude.False;
                                 (:) ctor ctors1 ->
                                  Datatypes.andb
                                    (Datatypes.andb
                                      (Names.eq_ScopedName name
                                        (Datatypes.fst ctor))
                                      (typecheck_eq ps0 ctx0 body rtype0))
                                    (typecheck_cases ps0 ctxs0 cases' rtype0
                                      bs_types0 ctors1)}}}}}
                       in typecheck_cases}
    in
    SumMonad.bind_sum (wrap_sum ctors) (\ctors0 ->
      case Datatypes.andb
             (Datatypes.andb bs_check
               (typecheck_eq ps ctx ex (Datatypes.fst qn)))
             (typecheck_cases ps
               (List.map (\ctor ->
                 Datatypes.app (Datatypes.snd ctor) bs_types) ctors0) cases
               rtype bs_types ctors0) of {
       Prelude.True -> Datatypes.Coq_inr rtype;
       Prelude.False -> dummy});
   AST.E_CoMatch qn bs cocases ->
    let {bs_types = List.map Datatypes.snd bs} in
    let {
     bs_check = List.forallb (\x ->
                  typecheck_eq ps ctx (Datatypes.fst x) (Datatypes.snd x)) bs}
    in
    let {
     typecheck_cocases = let {
                          typecheck_cocases _ ctxs cocases0 bs_types0 dtors =
                            case ctxs of {
                             [] ->
                              case cocases0 of {
                               [] ->
                                case dtors of {
                                 [] -> Prelude.True;
                                 (:) _ _ -> Prelude.False};
                               (:) _ _ -> Prelude.False};
                             (:) ctx0 ctxs0 ->
                              case cocases0 of {
                               [] -> Prelude.False;
                               (:) p cocases' ->
                                case p of {
                                 (,) name body ->
                                  case dtors of {
                                   [] -> Prelude.False;
                                   (:) dtor dtors' ->
                                    Datatypes.andb
                                      (Datatypes.andb
                                        (Names.eq_ScopedName name
                                          (Datatypes.fst
                                            (Datatypes.fst dtor)))
                                        (typecheck_eq ps ctx0 body
                                          (Datatypes.snd dtor)))
                                      (typecheck_cocases ps ctxs0 cocases'
                                        bs_types0 dtors')}}}}}
                         in typecheck_cocases}
    in
    SumMonad.bind_sum
      (wrap_sum (UtilsSkeleton.lookup_dtors ps (Datatypes.fst qn)))
      (\dtors ->
      case Datatypes.andb bs_check
             (typecheck_cocases ps
               (List.map (\dtor ->
                 Datatypes.app (Datatypes.snd (Datatypes.fst dtor)) bs_types)
                 dtors) cocases bs_types dtors) of {
       Prelude.True -> Datatypes.Coq_inr (Datatypes.fst qn);
       Prelude.False -> dummy});
   AST.E_Let e1 e2 ->
    SumMonad.bind_sum (typecheck ps ctx e1) (\t1 ->
      typecheck ps ((:) t1 ctx) e2)}

index_list :: Prelude.Integer -> ([] a1) -> [] ((,) AST.Coq_expr a1)
index_list n ls =
  case ls of {
   [] -> [];
   (:) head tail -> (:) ((,) (AST.E_Var n) head)
    (index_list ((Prelude.+ 1) n) tail)}

