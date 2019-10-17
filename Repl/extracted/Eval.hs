module Eval where

import qualified Prelude
import qualified AST
import qualified Basics
import qualified Datatypes
import qualified List
import qualified OptionMonad
import qualified ProgramDef
import qualified UtilsProgram

value_b :: AST.Coq_expr -> Prelude.Bool
value_b e =
  case e of {
   AST.E_Constr _ args -> List.forallb value_b args;
   AST.E_GenFunCall _ es -> List.forallb value_b es;
   AST.E_CoMatch _ bs _ ->
    List.forallb (Basics.compose value_b Datatypes.fst) bs;
   _ -> Prelude.False}

one_step_eval :: ProgramDef.Coq_program -> AST.Coq_expr -> Prelude.Maybe
                 AST.Coq_expr
one_step_eval p e =
  case e of {
   AST.E_Var _ -> Prelude.Nothing;
   AST.E_Constr n args ->
    OptionMonad.bind
      (let {
        apply_to_first_nonvalue es =
          case es of {
           [] -> Prelude.Nothing;
           (:) arg args' ->
            case value_b arg of {
             Prelude.True ->
              OptionMonad.bind (apply_to_first_nonvalue args') (\args'' ->
                OptionMonad.eta ((:) arg args''));
             Prelude.False ->
              OptionMonad.bind (one_step_eval p arg) (\arg' ->
                OptionMonad.eta ((:) arg' args'))}}}
       in apply_to_first_nonvalue args) (\args' ->
      OptionMonad.eta (AST.E_Constr n args'));
   AST.E_DestrCall sn ex args ->
    case value_b ex of {
     Prelude.True ->
      case List.forallb value_b args of {
       Prelude.True ->
        case ex of {
         AST.E_GenFunCall comatchfunname cargs ->
          OptionMonad.bind
            (UtilsProgram.lookup_gfun_bods_scoped p comatchfunname)
            (\cocases ->
            OptionMonad.bind
              (UtilsProgram.lookup_cocase (Datatypes.snd cocases) sn)
              (\body -> Prelude.Just
              (AST.multi_subst (Datatypes.app args cargs)
                (Datatypes.snd body))));
         AST.E_CoMatch _ bindings cocases ->
          OptionMonad.bind (UtilsProgram.lookup_cocase cocases sn) (\body ->
            Prelude.Just
            (AST.multi_subst
              (Datatypes.app args (List.map Datatypes.fst bindings))
              (Datatypes.snd body)));
         _ -> Prelude.Nothing};
       Prelude.False ->
        OptionMonad.bind
          (let {
            apply_to_first_nonvalue es =
              case es of {
               [] -> Prelude.Nothing;
               (:) arg args' ->
                case value_b arg of {
                 Prelude.True ->
                  OptionMonad.bind (apply_to_first_nonvalue args')
                    (\args'' -> Prelude.Just ((:) arg args''));
                 Prelude.False ->
                  OptionMonad.bind (one_step_eval p arg) (\arg' ->
                    Prelude.Just ((:) arg' args'))}}}
           in apply_to_first_nonvalue args) (\args' -> Prelude.Just
          (AST.E_DestrCall sn ex args'))};
     Prelude.False ->
      OptionMonad.bind (one_step_eval p ex) (\ex' -> Prelude.Just
        (AST.E_DestrCall sn ex' args))};
   AST.E_FunCall n args ->
    case List.forallb value_b args of {
     Prelude.True ->
      OptionMonad.bind (UtilsProgram.lookup_fun_bods p n) (\body ->
        Prelude.Just (AST.multi_subst args body));
     Prelude.False ->
      OptionMonad.bind
        (let {
          apply_to_first_nonvalue es =
            case es of {
             [] -> Prelude.Nothing;
             (:) arg args' ->
              case value_b arg of {
               Prelude.True ->
                OptionMonad.bind (apply_to_first_nonvalue args') (\args'' ->
                  Prelude.Just ((:) arg args''));
               Prelude.False ->
                OptionMonad.bind (one_step_eval p arg) (\arg' -> Prelude.Just
                  ((:) arg' args'))}}}
         in apply_to_first_nonvalue args) (\args' -> Prelude.Just
        (AST.E_FunCall n args'))};
   AST.E_GenFunCall qn args ->
    case List.forallb value_b args of {
     Prelude.True -> Prelude.Nothing;
     Prelude.False ->
      OptionMonad.bind
        (let {
          apply_to_first_nonvalue ars =
            case ars of {
             [] -> Prelude.Nothing;
             (:) arg args' ->
              case value_b arg of {
               Prelude.True ->
                OptionMonad.bind (apply_to_first_nonvalue args') (\args'' ->
                  Prelude.Just ((:) arg args''));
               Prelude.False ->
                OptionMonad.bind (one_step_eval p arg) (\arg' -> Prelude.Just
                  ((:) arg' args'))}}}
         in apply_to_first_nonvalue args) (\args' -> Prelude.Just
        (AST.E_GenFunCall qn args'))};
   AST.E_ConsFunCall sn ex args ->
    case value_b ex of {
     Prelude.True ->
      case List.forallb value_b args of {
       Prelude.True ->
        case ex of {
         AST.E_Constr name cargs ->
          OptionMonad.bind (UtilsProgram.lookup_cfun_bods_scoped p sn)
            (\body ->
            OptionMonad.bind
              (UtilsProgram.lookup_case (Datatypes.snd body) name) (\c ->
              Prelude.Just
              (AST.multi_subst (Datatypes.app cargs args) (Datatypes.snd c))));
         _ -> Prelude.Nothing};
       Prelude.False ->
        OptionMonad.bind
          (let {
            apply_to_first_nonvalue ars =
              case ars of {
               [] -> Prelude.Nothing;
               (:) arg args' ->
                case value_b arg of {
                 Prelude.True ->
                  OptionMonad.bind (apply_to_first_nonvalue args')
                    (\args'' -> Prelude.Just ((:) arg args''));
                 Prelude.False ->
                  OptionMonad.bind (one_step_eval p arg) (\arg' ->
                    Prelude.Just ((:) arg' args'))}}}
           in apply_to_first_nonvalue args) (\args' -> Prelude.Just
          (AST.E_ConsFunCall sn ex args'))};
     Prelude.False ->
      OptionMonad.bind (one_step_eval p ex) (\ex' -> Prelude.Just
        (AST.E_ConsFunCall sn ex' args))};
   AST.E_Match matchname ex bindings cases type0 ->
    case value_b ex of {
     Prelude.True ->
      let {args = List.map Datatypes.fst bindings} in
      case List.forallb value_b args of {
       Prelude.True ->
        case ex of {
         AST.E_Constr name cargs ->
          OptionMonad.bind (UtilsProgram.lookup_case cases name) (\c ->
            Prelude.Just
            (AST.multi_subst (Datatypes.app cargs args) (Datatypes.snd c)));
         _ -> Prelude.Nothing};
       Prelude.False ->
        OptionMonad.bind
          (let {
            apply_to_first_nonvalue bs =
              case bs of {
               [] -> Prelude.Nothing;
               (:) p0 args' ->
                case p0 of {
                 (,) arg argt ->
                  case value_b arg of {
                   Prelude.True ->
                    OptionMonad.bind (apply_to_first_nonvalue args')
                      (\args'' -> Prelude.Just ((:) ((,) arg argt) args''));
                   Prelude.False ->
                    OptionMonad.bind (one_step_eval p arg) (\arg' ->
                      Prelude.Just ((:) ((,) arg' argt) args'))}}}}
           in apply_to_first_nonvalue bindings) (\bindings' -> Prelude.Just
          (AST.E_Match matchname ex bindings' cases type0))};
     Prelude.False ->
      OptionMonad.bind (one_step_eval p ex) (\ex' -> Prelude.Just
        (AST.E_Match matchname ex' bindings cases type0))};
   AST.E_CoMatch comatchname bindings cocases ->
    case List.forallb value_b (List.map Datatypes.fst bindings) of {
     Prelude.True -> Prelude.Nothing;
     Prelude.False ->
      OptionMonad.bind
        (let {
          apply_to_first_nonvalue bs =
            case bs of {
             [] -> Prelude.Nothing;
             (:) p0 args' ->
              case p0 of {
               (,) arg argt ->
                case value_b arg of {
                 Prelude.True ->
                  OptionMonad.bind (apply_to_first_nonvalue args')
                    (\args'' -> Prelude.Just ((:) ((,) arg argt) args''));
                 Prelude.False ->
                  OptionMonad.bind (one_step_eval p arg) (\arg' ->
                    Prelude.Just ((:) ((,) arg' argt) args'))}}}}
         in apply_to_first_nonvalue bindings) (\bindings' -> Prelude.Just
        (AST.E_CoMatch comatchname bindings' cocases))};
   AST.E_Let e1 e2 ->
    case value_b e1 of {
     Prelude.True -> Prelude.Just (AST.substitute e1 e2);
     Prelude.False ->
      OptionMonad.bind (one_step_eval p e1) (\e1' -> Prelude.Just (AST.E_Let
        e1' e2))}}

