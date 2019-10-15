{-# LANGUAGE StandaloneDeriving #-}
module Plumbing where

import Names
import AST

-- The following code makes the extracted Haskell Code instances of the relevant typeclasses Show, Eq, etc.

-- AST.hs
instance Show ScopedName where
  show (Coq_local cs) = "_" ++ (show cs)
  show (Coq_global cs) = show cs

instance Eq ScopedName where
  (Coq_local cs) == (Coq_local cs') = (cs == cs')
  (Coq_global cs) == (Coq_global cs') = (cs == cs')
  _ == _ = False

deriving instance Show Coq_expr
deriving instance Eq Coq_expr
