module List where

import qualified Prelude
import qualified Datatypes

concat :: ([] ([] a1)) -> [] a1
concat l =
  case l of {
   [] -> [];
   (:) x l0 -> Datatypes.app x (concat l0)}

map :: (a1 -> a2) -> ([] a1) -> [] a2
map f l =
  case l of {
   [] -> [];
   (:) a t -> (:) (f a) (map f t)}

flat_map :: (a1 -> [] a2) -> ([] a1) -> [] a2
flat_map f l =
  case l of {
   [] -> [];
   (:) x t -> Datatypes.app (f x) (flat_map f t)}

forallb :: (a1 -> Prelude.Bool) -> ([] a1) -> Prelude.Bool
forallb f l =
  case l of {
   [] -> Prelude.True;
   (:) a l0 -> Datatypes.andb (f a) (forallb f l0)}

filter :: (a1 -> Prelude.Bool) -> ([] a1) -> [] a1
filter f l =
  case l of {
   [] -> [];
   (:) x l0 ->
    case f x of {
     Prelude.True -> (:) x (filter f l0);
     Prelude.False -> filter f l0}}

find :: (a1 -> Prelude.Bool) -> ([] a1) -> Prelude.Maybe a1
find f l =
  case l of {
   [] -> Prelude.Nothing;
   (:) x tl ->
    case f x of {
     Prelude.True -> Prelude.Just x;
     Prelude.False -> find f tl}}

combine :: ([] a1) -> ([] a2) -> [] ((,) a1 a2)
combine l l' =
  case l of {
   [] -> [];
   (:) x tl ->
    case l' of {
     [] -> [];
     (:) y tl' -> (:) ((,) x y) (combine tl tl')}}

