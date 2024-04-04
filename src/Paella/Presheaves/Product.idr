module Paella.Presheaves.Product

import Data.SnocList
import Data.SnocList.Extra
import Data.SnocList.Quantifiers
import Data.SnocList.Quantifiers.Extra

import Data.Fin

import Paella.Worlds
import Paella.Families
import Paella.Presheaves

%default total

-- Product structure

||| The product of families is given pointwise
public export
FamProd : SnocList Family -> Family
FamProd sf w = ForAll sf $ \f => f w

||| When each family in a product of families is a presheaf, then so is the
||| product
export
BoxCoalgProd : {sf : SnocList Family} ->
  ForAll sf BoxCoalg -> BoxCoalg $ FamProd sf
BoxCoalgProd scoalg = MkBoxCoalg $ \w, sx, w', rho =>
  zipPropertyWithRelevant (\f, coalg, x => coalg.map rho x) scoalg sx

||| Given a collection of maps out of a family `f`, we can tuple them together
export
tuple : {f : Family} -> {sg : SnocList Family} ->
  ForAll sg (\g => f -|> g) -> (f -|> FamProd sg)
tuple sh w x = mapProperty (\h => h w x) sh

||| Projection out of a product of families
projection : {sf : SnocList Family} ->
  (i : Fin $ length sf) -> FamProd sf -|> (sf !! i)
projection i w sx = indexAll (indexIsElem sf i) sx

||| Product of families is symmetric
export
swap : FamProd [< f, g] -|> FamProd [< g, f]
swap w [< x, y] = [< y, x]