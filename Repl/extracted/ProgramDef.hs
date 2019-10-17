module ProgramDef where

import qualified Prelude
import qualified BodyTypeDefs
import qualified Skeleton

data Coq_program =
   Coq_mkProgram Skeleton.Coq_skeleton BodyTypeDefs.Coq_fun_bods BodyTypeDefs.Coq_cfun_bods 
 BodyTypeDefs.Coq_cfun_bods BodyTypeDefs.Coq_gfun_bods BodyTypeDefs.Coq_gfun_bods

program_skeleton :: Coq_program -> Skeleton.Coq_skeleton
program_skeleton p =
  case p of {
   Coq_mkProgram program_skeleton0 _ _ _ _ _ -> program_skeleton0}

program_fun_bods :: Coq_program -> BodyTypeDefs.Coq_fun_bods
program_fun_bods p =
  case p of {
   Coq_mkProgram _ program_fun_bods0 _ _ _ _ -> program_fun_bods0}

program_cfun_bods_g :: Coq_program -> BodyTypeDefs.Coq_cfun_bods
program_cfun_bods_g p =
  case p of {
   Coq_mkProgram _ _ program_cfun_bods_g0 _ _ _ -> program_cfun_bods_g0}

program_cfun_bods_l :: Coq_program -> BodyTypeDefs.Coq_cfun_bods
program_cfun_bods_l p =
  case p of {
   Coq_mkProgram _ _ _ program_cfun_bods_l0 _ _ -> program_cfun_bods_l0}

program_gfun_bods_g :: Coq_program -> BodyTypeDefs.Coq_gfun_bods
program_gfun_bods_g p =
  case p of {
   Coq_mkProgram _ _ _ _ program_gfun_bods_g0 _ -> program_gfun_bods_g0}

program_gfun_bods_l :: Coq_program -> BodyTypeDefs.Coq_gfun_bods
program_gfun_bods_l p =
  case p of {
   Coq_mkProgram _ _ _ _ _ program_gfun_bods_l0 -> program_gfun_bods_l0}

emptyProgram :: Coq_program
emptyProgram =
  Coq_mkProgram Skeleton.emptySkeleton [] [] [] [] []

