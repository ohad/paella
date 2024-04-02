module Data.SnocList.Quantifiers.Extra

import Data.DPair

import Data.SnocList
import Data.SnocList.Elem
import Data.SnocList.Quantifiers

%default total

-- `Any` related functions

namespace Any
  ||| Swapped version of `Any`
  public export
  ForAny : SnocList a -> (0 _ : (a -> Type)) -> Type
  ForAny sx p = Any p sx

  ||| Inject an element satisfying the property into an `Any`
  export
  inject : {sx : SnocList a} -> {p : a -> Type} ->
    x `Elem` sx -> p x -> Any p sx
  inject Here px = Here px
  inject (There y) px = There (inject y px)

  ||| Move function from property to snoclist
  export
  propertyToMap : {0 sx : SnocList a} -> {0 f : a -> b} ->
    Any (p . f) sx -> Any p (map f sx)
  propertyToMap (Here y) = Here y
  propertyToMap (There y) = There (propertyToMap y)

  ||| Move function from snoclist to property
  export
  mapToProprety : {sx : SnocList a} -> {0 f : a -> b} ->
    Any p (map f sx) -> Any (p . f) sx
  mapToProprety {sx = [<]} _ impossible
  mapToProprety {sx = sx :< x} (Here y) = Here y
  mapToProprety {sx = sx :< x} (There y) = There (mapToProprety y)

  ||| Forget `Any` for a constant property
  export
  forget : {0 sx : SnocList _} -> Any (const type) sx -> type
  forget y = (toExists y).snd

-- `All` related functions

namespace All
  ||| Swapped version of `All`
  public export
  ForAll : SnocList a -> (0 _ : (a -> Type)) -> Type
  ForAll sx p = All p sx

  ||| Tabulate a snoclist into a snoclist of proofs given a way to construct 
  ||| proofs
  export
  tabulate : (sx : SnocList _) -> ((x : _) -> p x) -> All p sx
  tabulate [<] f = [<]
  tabulate (sx :< x) f = tabulate sx f :< f x

  ||| Tabulate a snoclist into a snoclist of proofs given a way to construct 
  ||| proofs which knows the element belongs to the snoclist
  export
  tabulateElem :
    (sx : SnocList _) ->
    ((x : _) -> x `Elem` sx -> p x) ->
    All p sx
  tabulateElem [<] f = [<]
  tabulateElem (sx :< x) f =
    tabulateElem sx (\x', y => f x' (There y)) :< f x Here

  ||| Move function from property to snoclist
  export
  propertyToMap : {0 sx : SnocList a} -> {0 f : a -> b} ->
    All (p . f) sx -> All p (map f sx)
  propertyToMap [<] = [<]
  propertyToMap (sx :< x) = propertyToMap sx :< x

  ||| Move function from snoclist to property
  export
  mapToProperty : {sx : SnocList a} -> {0 f : a -> b} ->
    All p (map f sx) -> All (p . f) sx
  mapToProperty {sx = [<]} [<] = [<]
  mapToProperty {sx = _ :< _} (sx :< x) = mapToProperty sx :< x

  ||| Combine two snoclists of properties with access to the element
  export
  zipPropertyWithRelevant : {sx : SnocList _} ->
    ((x : _) -> p x -> q x -> r x) -> All p sx -> All q sx -> All r sx
  zipPropertyWithRelevant f [<] [<] = [<]
  zipPropertyWithRelevant f (spx :< px) (sqx :< qx) =
    zipPropertyWithRelevant f spx sqx :< f _ px qx

  ||| Modify the property given a pointwise function with access to the element
  export
  mapPropertyWithRelevant : {sx : SnocList _} ->
    ((x : _) -> p x -> q x) -> All p sx -> All q sx
  mapPropertyWithRelevant f [<] = [<]
  mapPropertyWithRelevant f (spx :< px) =
    mapPropertyWithRelevant f spx :< f _ px

  export
  mapPropertyWithRelevant' : {sx : SnocList _} ->
    ((x : _) -> (p . f) x -> (q . g) x) -> All p (map f sx) -> All q (map g sx)
  mapPropertyWithRelevant' h spfx =
    propertyToMap $ mapPropertyWithRelevant h (mapToProperty spfx)

-- `Any` and `All` related functions

||| Given a snoclist with all elements satisfying `p`, an element satisfying
||| `q`, and a function for combining them, apply the function at the element
export
applyAtAny : {sx : SnocList _} ->
  ((x : _) -> p x -> q x -> r x) -> All p sx -> Any q sx -> Any r sx
applyAtAny f (sx :< x) (Here y) = Here (f _ x y)
applyAtAny f (sx :< x) (There y) = There (applyAtAny f sx y)

export
applyAtAny' : {sx : SnocList _} ->
  ((x : _) -> (p . f) x -> (q . g) x -> r x) ->
  All p (map f sx) -> Any q (map g sx) -> Any r sx
applyAtAny' h spfx qgx = applyAtAny h (mapToProperty spfx) (mapToProprety qgx)

export
applyAtAnyErased : {0 sx : SnocList _} ->
  ((0 x : _) -> p x -> q x -> r x) -> All p sx -> Any q sx -> Any r sx
applyAtAnyErased f (sx :< x) (Here y) = Here (f _ x y)
applyAtAnyErased f (sx :< x) (There y) = There (applyAtAnyErased f sx y)