module Data.SnocList.Quantifiers.Extra

import Data.DPair

import Data.SnocList
import Data.SnocList.Elem
import Data.SnocList.Quantifiers

-- `Any` related functions

namespace Any
  ||| Swapped version of `Any`
  public export
  ForAny :  SnocList a -> (0 _ : (a -> Type)) -> Type
  ForAny sx p = Any p sx

  ||| Inject an element satisfying the property into an `Any`
  export
  injectAny : {sx : SnocList a} -> {p : a -> Type} ->
    x `Elem` sx -> p x -> Any p sx
  injectAny Here px = Here px
  injectAny (There y) px = There (injectAny y px)

  ||| Move function from property to snoclist
  export
  rippleAny : {0 sx : SnocList a} -> {0 f : a -> b} ->
    Any (p . f) sx -> Any p (map f sx)
  rippleAny (Here y) = Here y
  rippleAny (There y) = There (rippleAny y)

  ||| Move function from snoclist to property
  export
  unrippleAny : {sx : SnocList a} -> {0 f : a -> b} ->
    Any p (map f sx) -> Any (p . f) sx
  unrippleAny {sx = [<]} _ impossible
  unrippleAny {sx = sx :< x} (Here y) = Here y
  unrippleAny {sx = sx :< x} (There y) = There (unrippleAny y)

  ||| Forget `Any` for a constant property
  export
  forgetAny : {0 sx : SnocList _} -> Any (const type) sx -> type
  forgetAny pos = (toExists pos).snd

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
  rippleAll : {0 sx : SnocList a} -> {0 f : a -> b} ->
    All (p . f) sx -> All p (map f sx)
  rippleAll [<] = [<]
  rippleAll (sx :< x) = rippleAll sx :< x

  ||| Move function from snoclist to property
  export
  unrippleAll : {sx : SnocList a} -> {0 f : a -> b} ->
    All p (map f sx) -> All (p . f) sx
  unrippleAll {sx = [<]} [<] = [<]
  unrippleAll {sx = _ :< _} (sx :< x) = unrippleAll sx :< x

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
  mapAll : {sx : SnocList _} ->
    ((x : _) -> (p . f) x -> (q . g) x) -> All p (map f sx) -> All q (map g sx)
  mapAll h spfx = rippleAll $ mapPropertyWithRelevant h (unrippleAll spfx)

-- `Any` and `All` related functions

||| Given a snoclist with all elements satisfying `p`, an element satisfying
||| `q`, and a function for combining them, apply the function at the element
export
applyAny : {sx : SnocList _} ->
  ((x : _) -> p x -> q x -> r x) -> All p sx -> Any q sx -> Any r sx
applyAny f (sx :< x) (Here y) = Here (f _ x y)
applyAny f (sx :< x) (There y) = There (applyAny f sx y)

export
applyMapAllAny : {sx : SnocList _} ->
  ((x : _) -> (p . f) x -> (q . g) x -> r x) ->
  All p (map f sx) -> Any q (map g sx) -> Any r sx
applyMapAllAny h spfx qgx = applyAny h (unrippleAll spfx) (unrippleAny qgx)

export
applyAnyErased : {0 sx : SnocList _} ->
  ((0 x : _) -> p x -> q x -> r x) -> All p sx -> Any q sx -> Any r sx
applyAnyErased f (sx :< x) (Here y) = Here (f _ x y)
applyAnyErased f (sx :< x) (There y) = There (applyAnyErased f sx y)