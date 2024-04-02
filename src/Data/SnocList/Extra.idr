module Data.SnocList.Extra

import Data.SnocList
import Data.SnocList.Elem

import Data.Fin

infix 3 !!, ?!

public export
(!!) : (xs : SnocList a) -> (Fin (length xs)) -> a
[<] !! pos impossible
(xs :< x) !!  FZ      = x
(xs :< x) !! (FS pos) = xs !! pos

public export
(?!) : (xs : SnocList a) -> (i : Fin (length xs)) ->
       (xs !! i) `Elem` xs
[<] ?! i impossible
(xs :< x) ?!  FZ = Here
(xs :< x) ?! (FS pos) = There (xs ?! pos)