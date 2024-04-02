module Data.List.Quantifiers.Extra

import public Data.List
import public Data.List.Elem
import public Data.List.Quantifiers

public export
ForAny :  List a -> (0 _ : (a -> Type)) -> Type
ForAny xs p = Any p xs
public export
ForAll :  List a -> (0 _ : (a -> Type)) -> Type
ForAll xs p = All p xs

public export
tabulate : (sx : List a) -> ((x : a) -> p x) -> ForAll sx p
tabulate [] f = []
tabulate (x :: xs) f = f x :: tabulate xs f

public export
tabulateElem : (xs : List a) -> ((x : a) -> x `Elem` xs -> p x) -> ForAll xs p
tabulateElem [] f = []
tabulateElem (x :: xs) f =
  f x Here :: tabulateElem xs (\y, pos => f y (There pos))

public export
zipPropertyWithRelevant : {xs : List _} ->
  ((x : _) -> p x -> q x -> r x) -> All p xs -> All q xs -> All r xs
zipPropertyWithRelevant f [] vs = []
zipPropertyWithRelevant f (u :: us) (v :: vs) =
  f _ u v :: zipPropertyWithRelevant f us vs

public export
mapPropertyWithRelevant : {xs : List _} ->
  ((x : _) -> p x -> q x) -> All p xs -> All q xs
mapPropertyWithRelevant f [] = []
mapPropertyWithRelevant f (y :: ys) =
  f _ y :: mapPropertyWithRelevant f ys