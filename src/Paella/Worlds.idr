module Paella.Worlds

%default total

------------------------------------------
-- The category of worlds of parameters --
------------------------------------------

||| The type of available parameter types.
||| In the final development, we will abstract/parameterise over this type.
public export
data A = P

||| A zero-th order context, (co)arities of operations are covariant presheaves
||| over worlds
public export
data World = Leaf | Node World (Maybe A) World

||| A `x : Var a w` is a first-order variable of paramter type `a` in `w`
public export
data Var : A -> World -> Type where
  Nil : Var a $ Node l (Just a) r
  L : Var a l -> Var a $ Node l d r
  R : Var a r -> Var a $ Node l d r

data Bit = O | I

insert : Bit -> (this, other : World) -> Maybe A -> World
insert O this other a = Node this a other
insert I this other a = Node other a this

(::) : (b : Bit) -> Var c this -> Var c (insert b this other d)
O :: xs = L xs
I :: xs = R xs

Ex1 : World
Ex1 =
  Node (Node Leaf (Just P) Leaf)
       Nothing
       ((Node (Node Leaf (Just P) Leaf) Nothing Leaf))

Ex11, Ex12 : Var P Ex1
Ex11 = [O]
Ex12 = [I, O]

{-
||| A variable in `w1 ++ w2` is either in `w1` or `w2`
export
split : {w2 : World} -> Var a (w1 ++ w2) -> Either (Var a w1) (Var a w2)
split {w2 = [<]} x = Left x
split {w2 = _ :< _} Here = Right Here
split {w2 = _ :< _} (There x) = bimap id There (split x)

public export
infixr 1 ~>

||| A renaming from `src` to `tgt`, sending each variable in `src` to a
||| variable in `tgt`, i.e. a morphism of worlds
public export
(~>) : (src, tgt : World) -> Type
w1 ~> w2 = (a : A) -> Var a w1 -> Var a w2

||| Identity renaming
export
id : w ~> w
id a x = x

||| Composition of renamings
export
(.) : w2 ~> w3 -> w1 ~> w2 -> w1 ~> w3
(.) f g a x = f a (g a x)

-- `(++)` is a coproduct in the category of worlds

||| Coproduct inclusion on the left
export
inl : {w2 : World} -> w1 ~> w1 ++ w2
inl {w2 = [<]} a x = x
inl {w2 = w2 :< b} a x = There (inl a x)

||| Coproduct inclusion on the right
export
inr : w2 ~> w1 ++ w2
inr {w2 = .(w2 :< a)} a Here = Here
inr {w2 = .(w2 :< b)} a (There x) = There (inr a x)

||| Coproduct cotupling
export
cotuple : {w2 : World} -> (w1 ~> w) -> (w2 ~> w) -> w1 ++ w2 ~> w
cotuple {w2 = [<]} f g a x = f a x
cotuple {w2 = w2 :< b} f g .(b) Here = g b Here
cotuple {w2 = w2 :< b} f g a (There x) = cotuple f (\c, y => g c (There y)) a x

||| Symmetry of coproduct
export
swapRen : {w1, w2 : World} -> (w1 ++ w2) ~> (w2 ++ w1)
swapRen = cotuple inr inl

||| Bifunctorial action of coproduct
export
bimap : {w1, w2, w1', w2' : World} ->
  (w1 ~> w1') -> (w2 ~> w2') -> (w1 ++ w2) ~> (w1' ++ w2')
bimap f g a x = case split x of
  Left  y => inl a (f a y)
  Right y => inr a (g a y)
-}
