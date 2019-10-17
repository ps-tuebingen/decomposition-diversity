module Bool where

import qualified Prelude

eqb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
eqb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False ->
    case b2 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}}

