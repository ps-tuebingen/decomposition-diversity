module Datatypes where

import qualified Prelude

data Coq_unit =
   Coq_tt

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb = (Prelude.&&)

negb :: Prelude.Bool -> Prelude.Bool
negb = Prelude.not

nat_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

nat_rec :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rec =
  nat_rect

data Coq_sum a b =
   Coq_inl a
 | Coq_inr b

fst :: ((,) a1 a2) -> a1
fst = Prelude.fst

snd :: ((,) a1 a2) -> a2
snd = Prelude.snd

length :: ([] a1) -> Prelude.Integer
length l =
  case l of {
   [] -> (0 :: Prelude.Integer);
   (:) _ l' -> (Prelude.+ 1) (length l')}

app :: ([] a1) -> ([] a1) -> [] a1
app = (Prelude.++)

