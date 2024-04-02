module Data.SnocList.Quantifiers.Extra

import public Data.DPair

import public Data.SnocList
import public Data.SnocList.Elem
import public Data.SnocList.Quantifiers

public export
ForAny :  SnocList a -> (0 _ : (a -> Type)) -> Type
ForAny sx p = Any p sx
public export
ForAll : SnocList a -> (0 p : (a -> Type)) -> Type
ForAll sx p = All p sx

public export
injectAny : {xs : SnocList a} -> {p : a -> Type} -> x `Elem` xs -> p x -> Any p xs
injectAny Here px = Here px
injectAny (There y) px = There (injectAny y px)

public export
tabulate : (sx : SnocList a) -> ((x : a) -> p x) -> ForAll sx p
tabulate [<] f = [<]
tabulate (sx :< x) f = tabulate sx f :< f x

public export
tabulateElem : (xs : SnocList a) -> ((x : a) -> x `Elem` xs -> p x) -> ForAll xs p
tabulateElem [<] f = [<]
tabulateElem (sx :< x) f = tabulateElem sx (\y, pos => f y (There pos)) :< f x Here

public export
rippleAll : {0 xs : SnocList a} -> {0 f : a -> b} -> ForAll xs (p . f) -> ForAll (map f xs) p
rippleAll [<] = [<]
rippleAll (sx :< x) = rippleAll sx :< x

public export
rippleAny : {0 xs : SnocList a} -> {0 f : a -> b} -> ForAny xs (p . f) -> ForAny (map f xs) p
rippleAny (Here x) = Here x
rippleAny (There x) = There (rippleAny x)

public export
unrippleAll : {xs : SnocList a} -> {0 f : a -> b} -> ForAll (map f xs) p -> ForAll xs (p . f)
unrippleAll sy with (xs)
  unrippleAll ([<]) | [<] = [<]
  unrippleAll (sy :< y) | (sx :< x) = unrippleAll sy :< y

public export
unrippleAny : {xs : SnocList a} -> {0 f : a -> b} -> ForAny (map f xs) p -> ForAny xs (p . f)
unrippleAny {xs = [<]} _ impossible
unrippleAny {xs = sx :< b} (Here  x  ) = Here x
unrippleAny {xs = sx :< b} (There pos) = There (unrippleAny pos)

public export
applyAny : {xs : SnocList _} ->
  ((x : _) -> p x -> q x -> r x) -> All p xs -> Any q xs -> Any r xs
applyAny f (sx :< x) (Here  u  ) = Here  (f _ x u)
applyAny f (sx :< x) (There pos) = There (applyAny f sx pos)

-- Putting these together results in a flexible version
public export
applyMapAllAny : {sx : SnocList a} ->
  ((x : a) -> (p . f) x -> (q . g) x -> r x) ->
  All p (map f sx) -> Any q (map g sx) -> Any r sx
applyMapAllAny h su pos = applyAny h (unrippleAll su) (unrippleAny pos)

public export
zipPropertyWithRelevant : {xs : SnocList _} ->
  ((x : _) -> p x -> q x -> r x) -> All p xs -> All q xs -> All r xs
zipPropertyWithRelevant f [<] vs = [<]
zipPropertyWithRelevant f (u :< us) (v :< vs) = zipPropertyWithRelevant f u v :< f _ us vs

public export
mapPropertyWithRelevant : {xs : SnocList _} ->
  ((x : _) -> p x -> q x) -> All p xs -> All q xs
mapPropertyWithRelevant f [<] = [<]
mapPropertyWithRelevant f (sy :< y) = mapPropertyWithRelevant f sy :< f _ y

public export
mapAll : {sx : SnocList a} ->
  ((x : a) -> (p . f) x -> (q . g) x) ->
  All p (map f sx) -> All q (map g sx)
mapAll h su = rippleAll $ mapPropertyWithRelevant h (unrippleAll su)

-- For completeness

public export
applyAnyErased : {0 xs : SnocList _} ->
  ((0 x : _) -> p x -> q x -> r x) -> All p xs -> Any q xs -> Any r xs
applyAnyErased f (sx :< x) (Here  u  ) = Here  (f _ x u)
applyAnyErased f (sx :< x) (There pos) = There (applyAnyErased f sx pos)

public export
forgetAny : {0 sx : SnocList a} -> Any (const type) sx -> type
forgetAny pos = (toExists pos).snd