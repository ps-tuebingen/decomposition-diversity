module Names where
import qualified Data.Char
import qualified Data.Bits

import qualified Prelude
import qualified Bool
import qualified Datatypes

type VarName = Prelude.Integer

type TypeName =
  Prelude.String
  -- singleton inductive, whose constructor was TName
  
type Name = Prelude.String

type QName = (,) TypeName Name

data ScopedName =
   Coq_local QName
 | Coq_global QName

unscope :: ScopedName -> QName
unscope sn =
  case sn of {
   Coq_local qn -> qn;
   Coq_global qn -> qn}

eq_ascii :: Prelude.Char -> Prelude.Char -> Prelude.Bool
eq_ascii a1 a2 =
  (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0) (Data.Bits.testBit (Data.Char.ord a) 1) (Data.Bits.testBit (Data.Char.ord a) 2) (Data.Bits.testBit (Data.Char.ord a) 3) (Data.Bits.testBit (Data.Char.ord a) 4) (Data.Bits.testBit (Data.Char.ord a) 5) (Data.Bits.testBit (Data.Char.ord a) 6) (Data.Bits.testBit (Data.Char.ord a) 7))
    (\b1 b2 b3 b4 b5 b6 b7 b8 ->
    (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0) (Data.Bits.testBit (Data.Char.ord a) 1) (Data.Bits.testBit (Data.Char.ord a) 2) (Data.Bits.testBit (Data.Char.ord a) 3) (Data.Bits.testBit (Data.Char.ord a) 4) (Data.Bits.testBit (Data.Char.ord a) 5) (Data.Bits.testBit (Data.Char.ord a) 6) (Data.Bits.testBit (Data.Char.ord a) 7))
      (\c1 c2 c3 c4 c5 c6 c7 c8 ->
      Datatypes.andb
        (Datatypes.andb
          (Datatypes.andb
            (Datatypes.andb
              (Datatypes.andb
                (Datatypes.andb
                  (Datatypes.andb (Bool.eqb b1 c1) (Bool.eqb b2 c2))
                  (Bool.eqb b3 c3)) (Bool.eqb b4 c4)) (Bool.eqb b5 c5))
            (Bool.eqb b6 c6)) (Bool.eqb b7 c7)) (Bool.eqb b8 c8))
      a2)
    a1

eq_string :: Prelude.String -> Prelude.String -> Prelude.Bool
eq_string s1 s2 =
  case s1 of {
   [] -> case s2 of {
          [] -> Prelude.True;
          (:) _ _ -> Prelude.False};
   (:) x1 s3 ->
    case s2 of {
     [] -> Prelude.False;
     (:) x2 s4 -> Datatypes.andb (eq_ascii x1 x2) (eq_string s3 s4)}}

eq_Name :: Name -> Name -> Prelude.Bool
eq_Name =
  eq_string

eq_TypeName :: TypeName -> TypeName -> Prelude.Bool
eq_TypeName =
  eq_Name

eq_QName :: QName -> QName -> Prelude.Bool
eq_QName qn1 qn2 =
  case qn1 of {
   (,) tn1 n1 ->
    case qn2 of {
     (,) tn2 n2 -> Datatypes.andb (eq_TypeName tn1 tn2) (eq_Name n1 n2)}}

eq_ScopedName :: ScopedName -> ScopedName -> Prelude.Bool
eq_ScopedName sn1 sn2 =
  case sn1 of {
   Coq_local qn1 ->
    case sn2 of {
     Coq_local qn2 -> eq_QName qn1 qn2;
     Coq_global _ -> Prelude.False};
   Coq_global qn1 ->
    case sn2 of {
     Coq_local _ -> Prelude.False;
     Coq_global qn2 -> eq_QName qn1 qn2}}

