module Paella.Worlds

import Data.Vect
import Data.Vect.Quantifiers

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

OneOf : Vect n Type -> Type
OneOf = Any id

-- Not sure we really need these --- time will tell!

||| A variable in `w1 ++ w2` is either in `w1` or `w2`
export
splitNothing : (p : Var a (Node l d r)) ->
  (dIsNota : Uninhabited (d = Just a)) =>
  Either (Var a l)
         (Var a r)
splitNothing [] @{dNOTa} = absurd @{dNOTa} Refl
splitNothing (L x) = Left  x
splitNothing (R x) = Right x

Ex21 : ?
Ex21 = splitNothing Ex11

Ex22 : ?
Ex22 = splitNothing Ex12

||| A variable in `w1 ++ w2` is either in `w1` or `w2`
export
splitJust : {w2 : World} -> (p : Var a (Node l (Just a) r)) ->
  OneOf [Var a l, p = [], Var a r]
splitJust []    = There $ Here  Refl
splitJust (L x) =                 Here x
splitJust (R x) = There $ There $ Here x


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

||| 'Weak' coproduct inclusion on the left
export
winl : w1 ~> Node w1 d w2
winl a x = L x

||| Coproduct inclusion on the left
export
inl : w1 ~> Node w1 Nothing w2
inl = winl

||| 'Weak' coproduct inclusion on the right
export
winr : w2 ~> Node w1 d w2
winr a x = R x

||| Coproduct inclusion on the right
export
inr : w2 ~> Node w1 Nothing w2
inr = winr


||| Coproduct cotupling
export
cotuple : (l ~> w) -> (r ~> w) -> Node l Nothing r ~> w
cotuple f g a x with (splitNothing x)
 cotuple f g a x | Left  y = f a y
 cotuple f g a x | Right y = g a y

||| Symmetry of coproduct
export
swapRen : (Node l Nothing r) ~> Node r Nothing l
swapRen = cotuple inr inl

-- Can try to reuse previous ones but then need to define a cotuple
-- appriopriately --- not sure it's worth it.

||| Bifunctorial action of weak coproduct
export
bimap :
  (w1 ~> w1') -> (w2 ~> w2') -> (Node w1 d w2) ~> (Node w1' d w2')
bimap f g a [] = []
bimap f g a (L x) = L (f a x)
bimap f g a (R x) = R (g a x)
