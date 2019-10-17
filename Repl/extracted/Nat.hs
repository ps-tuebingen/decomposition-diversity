module Nat where

import qualified Prelude

add :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add = (Prelude.+)

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub = \x y -> Prelude.max (x Prelude.- y) 0

eqb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.True)
      (\_ -> Prelude.False)
      m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.False)
      (\m' -> eqb n' m')
      m)
    n

leb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.True)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.False)
      (\m' -> leb n' m')
      m)
    n

ltb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
ltb n m =
  leb ((Prelude.+ 1) n) m

