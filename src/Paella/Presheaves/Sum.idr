module Paella.Presheaves.Sum

import Data.SnocList
import Data.SnocList.Quantifiers
import Data.SnocList.Quantifiers.Extra

import Paella.Worlds
import Paella.Families
import Paella.Presheaves
import Paella.Presheaves.Representable
import Paella.Presheaves.Product

%default total

-- Coproduct structure

||| When each family in a sum of families is a presheaf, then so is the sum
public export
FamSum : SnocList Family -> Family
FamSum sf w = ForAny sf $ \f => f w

||| Presheaf structure of sum presheaf
export
BoxCoalgSum : {sf : SnocList Family} ->
  ForAll sf BoxCoalg -> BoxCoalg $ FamSum sf
BoxCoalgSum salg =  MkBoxCoalg $ \w, sx, w', rho =>
  applyAtAny (\f, coalg => coalg.map rho) salg sx