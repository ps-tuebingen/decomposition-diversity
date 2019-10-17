module UtilsProgram where

import qualified Prelude
import qualified AST
import qualified BodyTypeDefs
import qualified Datatypes
import qualified List
import qualified Names
import qualified ProgramDef

lookup_fun_bods :: ProgramDef.Coq_program -> Names.Name -> Prelude.Maybe
                   BodyTypeDefs.Coq_fun_bod
lookup_fun_bods p n =
  let {
   lookupHelper bs =
     case bs of {
      [] -> Prelude.Nothing;
      (:) f fs ->
       case Names.eq_Name (Datatypes.fst f) n of {
        Prelude.True -> Prelude.Just (Datatypes.snd f);
        Prelude.False -> lookupHelper fs}}}
  in lookupHelper (ProgramDef.program_fun_bods p)

lookup_gfun_bods_x :: BodyTypeDefs.Coq_gfun_bods -> Names.QName ->
                      Prelude.Maybe BodyTypeDefs.Coq_gfun_bod_named
lookup_gfun_bods_x bodies qn =
  List.find (\body -> Names.eq_QName qn (Datatypes.fst body)) bodies

lookup_gfun_bods_g :: ProgramDef.Coq_program -> Names.QName -> Prelude.Maybe
                      BodyTypeDefs.Coq_gfun_bod_named
lookup_gfun_bods_g p qn =
  lookup_gfun_bods_x (ProgramDef.program_gfun_bods_g p) qn

lookup_gfun_bods_l :: ProgramDef.Coq_program -> Names.QName -> Prelude.Maybe
                      BodyTypeDefs.Coq_gfun_bod_named
lookup_gfun_bods_l p qn =
  lookup_gfun_bods_x (ProgramDef.program_gfun_bods_l p) qn

lookup_gfun_bods_scoped :: ProgramDef.Coq_program -> Names.ScopedName ->
                           Prelude.Maybe BodyTypeDefs.Coq_gfun_bod_named
lookup_gfun_bods_scoped p sn =
  case sn of {
   Names.Coq_local qn -> lookup_gfun_bods_l p qn;
   Names.Coq_global qn -> lookup_gfun_bods_g p qn}

lookup_cfun_bods_x :: BodyTypeDefs.Coq_cfun_bods -> Names.QName ->
                      Prelude.Maybe BodyTypeDefs.Coq_cfun_bod_named
lookup_cfun_bods_x bodies qn =
  List.find (\body -> Names.eq_QName qn (Datatypes.fst body)) bodies

lookup_cfun_bods_g :: ProgramDef.Coq_program -> Names.QName -> Prelude.Maybe
                      BodyTypeDefs.Coq_cfun_bod_named
lookup_cfun_bods_g p qn =
  lookup_cfun_bods_x (ProgramDef.program_cfun_bods_g p) qn

lookup_cfun_bods_l :: ProgramDef.Coq_program -> Names.QName -> Prelude.Maybe
                      BodyTypeDefs.Coq_cfun_bod_named
lookup_cfun_bods_l p qn =
  lookup_cfun_bods_x (ProgramDef.program_cfun_bods_l p) qn

lookup_cfun_bods_scoped :: ProgramDef.Coq_program -> Names.ScopedName ->
                           Prelude.Maybe BodyTypeDefs.Coq_cfun_bod_named
lookup_cfun_bods_scoped p sn =
  case sn of {
   Names.Coq_local qn -> lookup_cfun_bods_l p qn;
   Names.Coq_global qn -> lookup_cfun_bods_g p qn}

lookup_case :: ([] ((,) Names.ScopedName AST.Coq_expr)) -> Names.ScopedName
               -> Prelude.Maybe ((,) Names.ScopedName AST.Coq_expr)
lookup_case cs sn =
  List.find (\case0 -> Names.eq_ScopedName sn (Datatypes.fst case0)) cs

lookup_cocase :: ([] ((,) Names.ScopedName AST.Coq_expr)) -> Names.ScopedName
                 -> Prelude.Maybe ((,) Names.ScopedName AST.Coq_expr)
lookup_cocase ccs sn =
  List.find (\cocase -> Names.eq_ScopedName sn (Datatypes.fst cocase)) ccs

