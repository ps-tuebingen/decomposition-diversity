module XStructorize where

import AST
import Names
import ProgramDef

import LiftComatch
import InlineMatch
import InlineOrderCfuns
import DtorizeIII
import LiftMatch
import InlineComatch
import InlineOrderGfuns
import CtorizeIII

dtorize :: TypeName -> Coq_program -> Coq_program
dtorize tn =
  inline_gfuns_to_program
  . reorder_gfuns
  . (flip destructorize_program tn)
  . (flip lift_match_to_program tn)

ctorize :: TypeName -> Coq_program -> Coq_program
ctorize tn =
  inline_cfuns_to_program
 . reorder_cfuns
 . (flip constructorize_program tn)
 . (flip lift_comatch_to_program tn)
