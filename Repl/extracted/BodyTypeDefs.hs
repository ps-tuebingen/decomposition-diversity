module BodyTypeDefs where

import qualified Prelude
import qualified AST
import qualified Names

type Coq_fun_bod = AST.Coq_expr

type Coq_fun_bod_named = (,) Names.Name Coq_fun_bod

type Coq_fun_bods = [] Coq_fun_bod_named

type Coq_gfun_bod = [] ((,) Names.ScopedName AST.Coq_expr)

type Coq_gfun_bod_named = (,) Names.QName Coq_gfun_bod

type Coq_gfun_bods = [] Coq_gfun_bod_named

type Coq_cfun_bod = [] ((,) Names.ScopedName AST.Coq_expr)

type Coq_cfun_bod_named = (,) Names.QName Coq_cfun_bod

type Coq_cfun_bods = [] Coq_cfun_bod_named

