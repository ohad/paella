module Paella.Presheaves.Representable

import Data.SnocList
import Data.SnocList.Quantifiers
import Data.SnocList.Quantifiers.Extra

import Paella.Worlds
import Paella.Families
import Paella.Presheaves
import Paella.Presheaves.Product

%default total

-- Representable functors

||| The representable functor at `w`, so a map `Env w -|> f` is morally an
||| element of `f w` and thus `f` in environment `w`
public export 0
Env : p.world -> p.family
Env w = (w ~>)

||| Reprentable presheaves are presheaves
BoxCoalgEnv : {w1 : p.world} -> BoxCoalg (Env w1)
BoxCoalgEnv = MkBoxCoalg $ \w, rho, w', rho' => rho' . rho

-- Exponentiating by representables, transformed

||| Fiore-transform of presheaf exponentiation of `f` by Yoneda of `w1`
public export
(.shift) : p.world -> p.family -> p.family
w1.shift f w2 = f (w1 ++ w2)

||| Fiore-transform of presheaf exponentiation of `f` by Yoneda of `w1`, swapped
public export 0
(.shiftLeft) : p.world -> p.family -> p.family
w1.shiftLeft f w2 = f (w2 ++ w1)

||| Exponentiating a presheaf by a representable gives a presheaf
export
(.shiftCoalg) : {0 f : p.family} ->
  (w1 : p.world) -> BoxCoalg f -> BoxCoalg (w1.shift f)
w1.shiftCoalg coalg = MkBoxCoalg $ \w, x, w', rho =>
  coalg.map (bimap {w1 = w1} id rho) x

||| Exponentiating a presheaf by a representable gives a presheaf, swapped
export
(.shiftLeftCoalg) : {0 f : p.family} ->
  (w1 : p.world) -> BoxCoalg f -> BoxCoalg (w1.shiftLeft f)
w1.shiftLeftCoalg coalg = MkBoxCoalg $ \w, x, w', rho =>
  coalg.map (bimap {w2 = w1} rho id) x

||| `w1.shift f` is an exponential of `f` by `Env w1`, thus has an evaluation
export
(.evalRep) : {w1 : p.world} -> {0 f : p.family} -> (coalg : BoxCoalg f) ->
  FamProd [< w1.shift f, Env w1] -|> f
coalg.evalRep w [< u, rho] = coalg.map (cotuple rho id) u

||| `w1.shift g` is an exponential of `g` by `Env w1`, thus has an currying
export
(.curryRep) : {w1 : p.world} -> {0 f,g : p.family} -> (coalg : BoxCoalg f) ->
  (FamProd [< f, Env w1] -|> g) -> (f -|> w1.shift g)
coalg.curryRep alpha w u = alpha (w1 ++ w) [< coalg.map inr u, inl]

export
(.curryRep') : {w1 : p.world} -> {0 f, g : p.family} -> (coalg : BoxCoalg f) ->
  (FamProd [< Env w1, f] -|> g) -> (f -|> w1.shift g)
coalg.curryRep' alpha = coalg.curryRep (alpha . swap)

||| `w1.shift g` is an exponential of `g` by `Env w1`, thus has an uncurrying
export
(.uncurryRep) : {w1 : p.world} -> {0 g : p.family} -> (coalg : BoxCoalg g) ->
  (f -|> w1.shift g) -> (FamProd [< f, Env w1] -|> g)
coalg.uncurryRep beta w [< u, rho] = coalg.map (cotuple rho id) (beta w u)
