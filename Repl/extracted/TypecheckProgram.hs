module TypecheckProgram where

import qualified Prelude
import qualified AST
import qualified BodyTypeDefs
import qualified Datatypes
import qualified List
import qualified Names
import qualified ProgramDef
import qualified Skeleton
import qualified Typechecker
import qualified UtilsProgram

collapseList :: ([] (Prelude.Maybe a1)) -> [] a1
collapseList ls =
  case ls of {
   [] -> [];
   (:) o ls' ->
    case o of {
     Prelude.Just a -> (:) a (collapseList ls');
     Prelude.Nothing -> collapseList ls'}}

typecheckFunctions :: ProgramDef.Coq_program -> [] Prelude.String
typecheckFunctions prog =
  let {skeleton = ProgramDef.program_skeleton prog} in
  let {functionSigs = Skeleton.skeleton_fun_sigs skeleton} in
  let {
   typecheckSingleFunction = \fun_sig ->
    case fun_sig of {
     (,) p rtype ->
      case p of {
       (,) fname args ->
        case UtilsProgram.lookup_fun_bods prog fname of {
         Prelude.Just bod ->
          case Typechecker.typecheck skeleton args bod of {
           Datatypes.Coq_inl _ -> Prelude.Just fname;
           Datatypes.Coq_inr tc_type ->
            case Names.eq_TypeName tc_type rtype of {
             Prelude.True -> Prelude.Nothing;
             Prelude.False -> Prelude.Just fname}};
         Prelude.Nothing -> Prelude.Nothing}}}}
  in
  collapseList (List.map typecheckSingleFunction functionSigs)

typecheckGfunBod :: Skeleton.Coq_skeleton -> Names.QName ->
                    Typechecker.Coq_ctxt -> BodyTypeDefs.Coq_gfun_bod ->
                    Prelude.Bool
typecheckGfunBod sk qn ctx g =
  let {bindingList = Typechecker.index_list (0 :: Prelude.Integer) ctx} in
  let {x = AST.E_CoMatch qn bindingList g} in
  case Typechecker.typecheck sk ctx x of {
   Datatypes.Coq_inl _ -> Prelude.False;
   Datatypes.Coq_inr tc_type -> Names.eq_TypeName (Datatypes.fst qn) tc_type}

typecheckGeneratorFunctions :: ProgramDef.Coq_program -> [] Prelude.String
typecheckGeneratorFunctions prog =
  let {skeleton = ProgramDef.program_skeleton prog} in
  let {gfunSigs = Skeleton.skeleton_gfun_sigs_g skeleton} in
  let {
   typecheckSingleFunction = \gfun_sig ->
    case gfun_sig of {
     (,) q args ->
      case q of {
       (,) tn n ->
        case UtilsProgram.lookup_gfun_bods_g prog ((,) tn n) of {
         Prelude.Just g ->
          case g of {
           (,) qn bod ->
            case typecheckGfunBod skeleton qn args bod of {
             Prelude.True -> Prelude.Nothing;
             Prelude.False -> Prelude.Just n}};
         Prelude.Nothing -> Prelude.Nothing}}}}
  in
  collapseList (List.map typecheckSingleFunction gfunSigs)

typecheckCfunBod :: Skeleton.Coq_skeleton -> Names.QName ->
                    Typechecker.Coq_ctxt -> BodyTypeDefs.Coq_cfun_bod ->
                    Names.TypeName -> Prelude.Bool
typecheckCfunBod sk qn ctx c rtype =
  let {
   bindingList = Typechecker.index_list ((Prelude.+ 1)
                   (0 :: Prelude.Integer)) ctx}
  in
  let {
   x = AST.E_Match qn (AST.E_Var (0 :: Prelude.Integer)) bindingList c rtype}
  in
  case Typechecker.typecheck sk ((:) (Datatypes.fst qn) ctx) x of {
   Datatypes.Coq_inl _ -> Prelude.False;
   Datatypes.Coq_inr tc_type -> Names.eq_TypeName tc_type rtype}

typecheckConsumerFunctions :: ProgramDef.Coq_program -> [] Prelude.String
typecheckConsumerFunctions prog =
  let {skeleton = ProgramDef.program_skeleton prog} in
  let {cfunSigs = Skeleton.skeleton_cfun_sigs_g skeleton} in
  let {
   typecheckSingleFunction = \cfun_sig ->
    case cfun_sig of {
     (,) p rtype ->
      case p of {
       (,) q args ->
        case q of {
         (,) tn n ->
          case UtilsProgram.lookup_cfun_bods_g prog ((,) tn n) of {
           Prelude.Just c ->
            case c of {
             (,) qn bod ->
              case typecheckCfunBod skeleton qn args bod rtype of {
               Prelude.True -> Prelude.Nothing;
               Prelude.False -> Prelude.Just n}};
           Prelude.Nothing -> Prelude.Nothing}}}}}
  in
  collapseList (List.map typecheckSingleFunction cfunSigs)

typecheckProgram :: ProgramDef.Coq_program -> (,)
                    ((,) ([] Prelude.String) ([] Prelude.String))
                    ([] Prelude.String)
typecheckProgram prog =
  let {funsTC = typecheckFunctions prog} in
  let {gfunsTC = typecheckGeneratorFunctions prog} in
  let {cfunsTC = typecheckConsumerFunctions prog} in
  (,) ((,) funsTC gfunsTC) cfunsTC

