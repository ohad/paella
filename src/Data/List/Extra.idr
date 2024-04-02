module Data.List.Extra

import Data.List
import Data.List.Elem

import Data.Fin

infix 3 !!, ?!

public export
(!!) : (xs : List a) -> (Fin (length xs)) -> a
xs !! i = index' xs i

public export
(?!) : (xs : List a) -> (i : Fin (length xs)) ->
       (xs !! i) `Elem` xs
[] ?! i impossible
(x :: xs) ?!  FZ = Here
(x :: xs) ?! (FS pos) = There (xs ?! pos)