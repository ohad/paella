module Paella.Presheaves.Exponential

import Data.SnocList
import Data.SnocList.Quantifiers
import Data.SnocList.Quantifiers.Extra

import Paella.Worlds
import Paella.Families
import Paella.Presheaves
import Paella.Presheaves.Representable
import Paella.Presheaves.Product

%default total

-- General exponential of presheaves

public export
infixr 2 -%

||| Exponential of presheaves
public export 0
(-%) : (f, g : p.family) -> p.family
(f -% g) w = (FamProd [< Env w, f]) -|> g

||| Evaluation for exponential
export
eval : FamProd [< f -% g, f] -|> g
eval w [< alpha, x] = alpha w [< id, x]

||| Currying for exponential
export
(.curry) : {0 h : p.family} -> (coalg : BoxCoalg h) ->
  (FamProd [< h, f] -|> g) -> (h -|> (f -% g))
coalg.curry beta w env w' [< rho, x] = beta w' [< coalg.map rho env, x]

||| Uncurrying for exponential
export
uncurry : {0 h : p.family} -> (h -|> (f -% g)) -> (FamProd [< h, f] -|> g)
uncurry h w [< env, x] = h w env w [< id, x]

||| The exponential of two presheaves is a presheaf
export
BoxCoalgExp : BoxCoalg (f -% g)
BoxCoalgExp = MkBoxCoalg $ \w, alpha, w', rho, w'', [< rho', x] =>
  alpha w'' [< rho' . rho, x]

||| Post-composition for exponentiating
export
expMap : {0 f, g, h : p.family} ->
  (f -|> g) -> (h -% f -|> h -% g)
expMap {f, g, h} alpha = BoxCoalgExp .curry (alpha . eval)

||| Swap the arguments of a curried function
-- instead of mess around with point-free style, switch to pointed style
export
(.swapExps) : {0 f, g, h : p.family} -> (coalg : BoxCoalg g) ->
  f -% (g -% h) -|> g -% (f -% h)
coalg.swapExps =
  (BoxCoalgExp).curry $ (BoxCoalgProd [< BoxCoalgExp , coalg]).curry $
    \w, [<[< a, y], x] => eval w [< eval w [< a, x], y]

||| Turn a real exponential by a representable into the special case
export
shiftIntoRepr : {w1 : p.world} -> {0 g : p.family} ->
  (Env w1 -% g) -|> (w1.shift g)
shiftIntoRepr = BoxCoalgExp .curryRep eval

||| Turn the special case of exponentiating by a representable into a real
||| exponential
export
(.shiftFromRepr) : {w1 : p.world} -> {g : p.family} -> (coalg : BoxCoalg g) ->
   (w1.shift g) -|> (Env w1 -% g)
coalg.shiftFromRepr = (w1.shiftCoalg coalg).curry coalg.evalRep
