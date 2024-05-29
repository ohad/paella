module Paella.Worlds

import Data.Vect
import Data.Vect.Quantifiers

import Deriving.Foldable
import Deriving.Functor
%hide Data.Morphisms.(~>)

%language ElabReflection
%default total

------------------------------------------
-- The category of worlds of parameters --
------------------------------------------

||| The type of available parameter types.
||| In the final development, we will abstract/parameterise over this type.
public export
data A = P

||| A tree data type which is the basis of our worlds
public export
data Tree a = Leaf | Node (Tree a) (Maybe a) (Tree a)

||| `Tree` is a functor
public export
Functor Tree where
  map f Leaf                = Leaf
  map f (Node l Nothing r)  = Node (map f l) Nothing      (map f r)
  map f (Node l (Just x) r) = Node (map f l) (Just (f x)) (map f r)

treeFoldable : Foldable Tree
treeFoldable = %runElab derive

||| `Tree` is foldable
public export
Foldable Tree where
  foldr = foldr @{treeFoldable}

-- Foldable Tree where
--   foldr func init Leaf = init
--   foldr func init (Node l Nothing r) = ?res_2
--   foldr func init (Node l (Just x) r) = ?res_3

||| A zero-th order context, (co)arities of operations are covariant presheaves
||| over worlds
public export
World : Type
World = Tree A

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

public export
(++) :
  World -> World -> World
l ++ r = Node l Nothing r

namespace All
  public export
  MaybeP : (p : (a -> Type)) -> Maybe a -> Type
  MaybeP p Nothing = Unit
  MaybeP p (Just x) = p x

  ||| A proof that all elements of a tree satisfy a property. It is a tree of
  ||| proofs, corresponding element-wise to the `Tree`.
  public export
  data All : (0 _ : (a -> Type)) -> Tree a -> Type where
    Leaf : All p Leaf
    {-
    NodeJ : All p l -> p x  -> All p r -> All p (Node l (Just x) r)
    NodeN : All p l -> Unit -> All p r -> All p (Node l Nothing r)
    -}
    Node : All p l -> MaybeP p mx -> All p r -> All p (Node l mx r)

  ||| Flipped version of `All`
  public export
  ForAll :  Tree a -> (0 _ : (a -> Type)) -> Type
  ForAll t p = All p t

namespace AllM
  public export
  data AllM : (0 _ : (Maybe a -> Type)) -> Tree a -> Type where
    Leaf : AllM p Leaf
    {-
    NodeJ : All p l -> p x  -> All p r -> All p (Node l (Just x) r)
    NodeN : All p l -> Unit -> All p r -> All p (Node l Nothing r)
    -}
    Node : AllM p l -> p mx -> AllM p r -> AllM p (Node l mx r)

  ||| Flipped version of `All`
  public export
  ForAllM :  Tree a -> (0 _ : (Maybe a -> Type)) -> Type
  ForAllM t p = AllM p t

  export
  mapProperty : {t : Tree _} ->
    ({0 mx : _} -> p mx -> q mx) -> AllM p t -> AllM q t
  mapProperty f Leaf = Leaf
  mapProperty f (Node l x r) =
    Node (mapProperty f l) (f x) (mapProperty f r)

  export
  mapPropertyWithRelevant : {t : Tree _} ->
    ((mx : _) -> p mx -> q mx) -> AllM p t -> AllM q t
  mapPropertyWithRelevant f Leaf = Leaf
  mapPropertyWithRelevant f (Node l x r) =
    Node (mapPropertyWithRelevant f l) (f _ x) (mapPropertyWithRelevant f r)