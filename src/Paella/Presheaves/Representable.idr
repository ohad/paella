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
public export
Env : World -> Family
Env w = (w ~>)

||| Reprentable presheaves are presheaves
export
BoxCoalgEnv : {w1 : World} -> BoxCoalg (Env w1)
BoxCoalgEnv = MkBoxCoalg $ \w, rho, w', rho' => rho' . rho
