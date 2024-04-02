module Paella.Presheaves.Sum

import Data.SnocList
import Data.SnocList.Quantifiers
import Data.SnocList.Quantifiers.Extra

import Paella.Worlds
import Paella.Families
import Paella.Presheaves
import Paella.Presheaves.Representable
import Paella.Presheaves.Product

-- Coproduct structure

||| When each family in a sum of families is a presheaf, then so is the sum
public export
FamSum : SnocList Family -> Family
FamSum sf w = ForAny sf $ \f => f w

||| Presheaf structure of sum presheaf
public export
BoxCoalgSum : {sf : SnocList Family} ->
  ForAll sf BoxCoalg -> BoxCoalg $ FamSum sf
BoxCoalgSum salg =  MkBoxCoalg $ \w, sx, w', rho =>
  applyAtAny (\f, coalg => coalg.map rho) salg sx

-- Exponentiating by a sum of representables, as a product

infixl 7 ^

||| The exponentiation of `f` by the sum of representables of `ws`
public export
(^) : Family -> SnocList World -> Family
f ^ ws = FamProd (map (\w => w.shift f) ws)

||| Exponentiating a presheaf by a sum of representables gives a presheaf
public export
BoxCoalgExpSum : {f : Family} -> {ws : SnocList World} ->
  BoxCoalg f -> BoxCoalg (f ^ ws)
BoxCoalgExpSum coalg =
  BoxCoalgProd $ propertyToMap $ tabulate _ $ \w => w.shiftCoalg coalg

||| Exponentiating by a sum of representables has an evaluation
public export
(.evalSum) : {ws : SnocList World} -> {f : Family} -> (coalg : BoxCoalg f) ->
  FamProd [< f ^ ws, FamSum (map Env ws)] -|> f
coalg.evalSum w [< u, rho] =
  forget $ applyAtAny' (\_, x, rho' => coalg.map (cotuple rho' id) x) u rho

||| Exponentiating by a sum of representables has a currying
public export
(.currySum) : {ws : SnocList World} -> {f : Family} -> (coalg : BoxCoalg f) ->
  (FamProd [< f, FamSum (map Env ws)] -|> g) -> (f -|> g ^ ws)
coalg.currySum {ws = [<]} alpha w u = [<]
coalg.currySum {ws = ws' :< w'} alpha w u =
  propertyToMap $ tabulateElem (ws' :< w') (\w1, pos =>
    alpha (w1 ++ w)
      [< coalg.map inr u
      ,  propertyToMap {sx = ws' :< w'} {f = Env} (inject pos inl)
      ]
  )

||| Exponentiating by a sum of representables has an uncurrying
public export
(.uncurrySum) : {ws : SnocList World} -> {g : Family} -> (coalg : BoxCoalg g) ->
  (f -|> g ^ ws) -> (FamProd [< f, FamSum (map Env ws)] -|> g)
coalg.uncurrySum beta w [< u, rho] = forget $
  applyAtAny' (\_, x, rho' => coalg.map (cotuple rho' id) x) (beta w u) rho

||| Post-composition for exponentiating by a sum of representables
public export
expSumMap : {ws : SnocList World} -> {f, g : Family} ->
  (f -|> g) -> (f ^ ws -|> g ^ ws)
expSumMap alpha w sx = mapPropertyWithRelevant' (\x, y => alpha (x ++ w) y) sx