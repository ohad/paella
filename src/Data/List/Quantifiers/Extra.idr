module Data.List.Quantifiers.Extra

import Data.List
import Data.List.Elem
import Data.List.Quantifiers

-- `Any` related functions

namespace Any
  ||| Swapped version of `Any`
  public export
  ForAny :  List a -> (0 _ : (a -> Type)) -> Type
  ForAny xs p = Any p xs

-- `All` related functions

namespace All
  ||| Swapped version of `All`
  public export
  ForAll :  List a -> (0 _ : (a -> Type)) -> Type
  ForAll xs p = All p xs

  ||| Tabulate a list into a list of proofs given a way to construct proofs
  export
  tabulate : (xs : List _) -> ((x : _) -> p x) -> All p xs
  tabulate [] f = []
  tabulate (x :: xs) f = f x :: tabulate xs f

  ||| Tabulate a list into a list of proofs given a way to construct proofs 
  ||| which knows the element belongs to the list
  export
  tabulateElem : (xs : List _) -> ((x : _) -> x `Elem` xs -> p x) -> All p xs
  tabulateElem [] f = []
  tabulateElem (x :: xs) f =
    f x Here :: tabulateElem xs (\x', y => f x' (There y))

  ||| Combine two lists of properties with access to the element
  export
  zipPropertyWithRelevant : {xs : List _} ->
    ((x : _) -> p x -> q x -> r x) -> All p xs -> All q xs -> All r xs
  zipPropertyWithRelevant f [] [] = []
  zipPropertyWithRelevant f (px :: pxs) (qx :: qxs) =
    f _ px qx :: zipPropertyWithRelevant f pxs qxs

  ||| Modify the property given a pointwise function with access to the element
  export
  mapPropertyWithRelevant : {xs : List _} ->
    ((x : _) -> p x -> q x) -> All p xs -> All q xs
  mapPropertyWithRelevant f [] = []
  mapPropertyWithRelevant f (px :: pxs) =
    f _ px :: mapPropertyWithRelevant f pxs