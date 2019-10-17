module OptionMonad where

import qualified Prelude

eta :: a1 -> Prelude.Maybe a1
eta a =
  Prelude.Just a

bind :: (Prelude.Maybe a1) -> (a1 -> Prelude.Maybe a2) -> Prelude.Maybe a2
bind a f =
  case a of {
   Prelude.Just a' -> f a';
   Prelude.Nothing -> Prelude.Nothing}

