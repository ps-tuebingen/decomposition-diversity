module SumMonad where

import qualified Prelude
import qualified Datatypes

bind_sum :: (Datatypes.Coq_sum a3 a1) -> (a1 -> Datatypes.Coq_sum a3 
            a2) -> Datatypes.Coq_sum a3 a2
bind_sum a f =
  case a of {
   Datatypes.Coq_inl x -> Datatypes.Coq_inl x;
   Datatypes.Coq_inr a' -> f a'}

