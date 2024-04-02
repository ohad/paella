module Data.List.Extra

import Data.List
import Data.List.Elem

import Data.Fin

||| Proof that the `i`th element of a list is an element of it
export
indexIsElem : (xs : List a) -> (i : Fin (length xs)) -> (index' xs i) `Elem` xs
indexIsElem [] i impossible
indexIsElem (x :: xs) FZ = Here
indexIsElem (x :: xs) (FS n) = There (indexIsElem xs n)