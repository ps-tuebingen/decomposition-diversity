module PeanoNat where

import qualified Prelude
import qualified Datatypes
import qualified Specif

_Nat__eqb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
_Nat__eqb n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.True)
      (\_ -> Prelude.False)
      m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.False)
      (\m' -> _Nat__eqb n' m')
      m)
    n

_Nat__leb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
_Nat__leb n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.True)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.False)
      (\m' -> _Nat__leb n' m')
      m)
    n

_Nat__ltb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
_Nat__ltb n m =
  _Nat__leb ((Prelude.+ 1) n) m

_Nat__eq_dec :: Prelude.Integer -> Prelude.Integer -> Specif.Coq_sumbool
_Nat__eq_dec n =
  Datatypes.nat_rec (\m ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Specif.Coq_left)
      (\_ -> Specif.Coq_right)
      m) (\_ iHn m ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Specif.Coq_right)
      (\m0 -> iHn m0)
      m) n

