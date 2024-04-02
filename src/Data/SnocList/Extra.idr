module Data.SnocList.Extra

import Data.SnocList
import Data.SnocList.Elem

import Data.Fin

||| Find a particular element of a snoclist
export
index' : (sx : SnocList a) -> (Fin (length sx)) -> a
index' [<] pos impossible
index' (sx :< x) FZ = x
index' (sx :< x) (FS n) = index' sx n

||| Proof that the `i`th element of a snoclist is an element of it
export
indexIsElem :
  (sx : SnocList a) ->
  (i : Fin (length sx)) ->
  (index' sx i) `Elem` sx
indexIsElem [<] i impossible
indexIsElem (sx :< x) FZ = Here
indexIsElem (sx :< x) (FS n) = There (indexIsElem sx n)