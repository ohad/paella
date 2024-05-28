module GoodTree

-- Breadth-first filled trees

||| Where is the next free location, Here, or the Left or Right subtree?
data Loc = H | L | R

||| Status of a node, either is Absent a value with directions to next free
||| location, or has a value present
data Status a = Absent Loc | Present a

namespace Path
  ||| Path relation to the next free location
  public export
  data Path : Status a -> Maybe Loc -> Maybe Loc -> Type where
    F : Path (Present a) Nothing  Nothing
    H : Path (Absent H)  Nothing  Nothing
    R : Path (Absent R)  Nothing  (Just r)
    L : Path (Absent L)  (Just l) (Just r)

||| Given a path relation, is there a free location?
free : Path s l r -> Maybe Loc
free F = Nothing
free H = Just H
free R = Just R
free L = Just L

||| A breadth-first filled tree, annoted with where the next free location is
data Tree : Type -> Maybe Loc -> Type where
  Leaf : Tree a Nothing
  Node : {0 l, r : Maybe Loc} ->
    (s : Status a) -> {0 c : Path s l r} ->
    Tree a l -> Tree a r -> Tree a (free c)

Ex1 : Tree Bool Nothing
Ex1 = Node (Present True) {c = F} Leaf Leaf

Ex2 : Tree Bool Nothing
Ex2 = Node (Present False) {c = F} Ex1 Ex1

Ex3 : Tree Bool (Just H)
Ex3 = Node (Absent H) {c = H} Leaf Leaf

Ex4 : Tree Bool (Just L)
Ex4 = Node (Absent L) {c = L} Ex3 Ex3

Ex5 : Tree Bool (Just R)
Ex5 = Node (Absent R) {c = R} Ex1 Ex3

namespace Var
  ||| Pointer to a value of type `a`
  public export
  data Var : a -> Tree a ml -> Type where
    Nil : Var a $ Node (Present a) {c = F} l r
    L   : Var a l -> Var a $ Node s {c = c'} l r
    R   : Var a r -> Var a $ Node s {c = c'} l r

namespace Free
  ||| Pointer to the next free location
  public export
  data Free : Tree a ml -> Type where
    Nil : Free $ Node (Absent H) {c = H} l r
    L   : Free l -> Free $ Node (Absent L) {c = L} l r
    R   : Free r -> Free $ Node (Absent R) {c = R} l r

Ex11 : Var True Ex1
Ex11 = []

Ex21 : List (Var True Ex2)
Ex21 = [L [], R []]

Ex31 : Free Ex3
Ex31 = []

-- Only one valid free location!
Ex41 : Free Ex4
Ex41 = L []

{- Don't type check
Ex41H : Free Ex4
Ex41H = []

Ex41R : Free Ex4
Ex41R = R []
-}

-- Only one valid location again
Ex51 : Free Ex5
Ex51 = R []

Ex52 : Var True Ex5
Ex52 = L []

public export
infixr 1 ~>

||| A renaming from `src` to `tgt`, sending each variable in `src` to a
||| variable in `tgt`, i.e. a morphism of worlds
(~>) : {A : Type} -> (src : Tree A ls) -> (tgt : Tree A lt) -> Type
w1 ~> w2 = (a : A) -> Var a w1 -> Var a w2

||| Identity renaming
id : w ~> w
id a x = x

||| Composition of renamings
export
(.) : w2 ~> w3 -> w1 ~> w2 -> w1 ~> w3
(.) f g a x = f a (g a x)

-- Each have one `True` value
Ex1to5 : Ex1 ~> Ex5
Ex1to5 True [] = L []

-- Each have one `True` value
Ex5to1 : Ex5 ~> Ex1
Ex5to1 True (L []) = []
Ex5to1 True (L _) impossible
Ex5to1 True (R (L _)) impossible
Ex5to1 True (R (R _)) impossible
Ex5to1 False (L _) impossible
Ex5to1 False (R (L _)) impossible
Ex5to1 False (R (R _)) impossible

-- Both are empty
Ex3to4 : Ex3 ~> Ex4
Ex3to4 _ (L _) impossible
Ex3to4 _ (R _) impossible

-- Both are empty
Ex4to3 : Ex4 ~> Ex3
Ex4to3 _ (L (L _)) impossible
Ex4to3 _ (L (R _)) impossible
Ex4to3 _ (R (L _)) impossible
Ex4to3 _ (R (L _)) impossible
Ex4to3 _ (R (R _)) impossible