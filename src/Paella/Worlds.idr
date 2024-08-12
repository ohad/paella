module Paella.Worlds

%default total

------------------------------------------
-- The category of worlds of parameters --
------------------------------------------

||| A zero-th order context, (co)arities of operations are covariant presheaves
||| over worlds
public export
(.world) : Type -> Type
p .world = SnocList p

||| A `x : Var a w` is a first-order variable of paramter type `a` in `w`
public export
data Var : p -> p.world -> Type where
  Here : Var a (w :< a)
  There : Var a w -> Var a (w :< b)

||| A variable in `w1 ++ w2` is either in `w1` or `w2`
export
split : {w2 : p.world} -> Var a (w1 ++ w2) -> Either (Var a w1) (Var a w2)
split {w2 = [<]} x = Left x
split {w2 = _ :< _} Here = Right Here
split {w2 = _ :< _} (There x) = bimap id There (split x)

public export
infixr 1 ~>

||| A renaming from `src` to `tgt`, sending each variable in `src` to a
||| variable in `tgt`, i.e. a morphism of worlds
public export 0
(~>) : (src, tgt : p.world) -> Type
(w1 ~> w2) {p} = (a : p) -> Var a w1 -> Var a w2

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
inl : {w2 : p.world} -> w1 ~> w1 ++ w2
inl {w2 = [<]} a x = x
inl {w2 = w2 :< b} a x = There (inl a x)

||| Coproduct inclusion on the right
export
inr : w2 ~> w1 ++ w2
inr {w2 = .(w2 :< a)} a Here = Here
inr {w2 = .(w2 :< b)} a (There x) = There (inr a x)

||| Coproduct cotupling
export
cotuple : {w2 : p.world} -> (w1 ~> w) -> (w2 ~> w) -> w1 ++ w2 ~> w
cotuple {w2 = [<]} f g a x = f a x
cotuple {w2 = w2 :< b} f g .(b) Here = g b Here
cotuple {w2 = w2 :< b} f g a (There x) = cotuple f (\c, y => g c (There y)) a x

||| Symmetry of coproduct
export
swapRen : {w1, w2 : p.world} -> (w1 ++ w2) ~> (w2 ++ w1)
swapRen = cotuple inr inl

||| Bifunctorial action of coproduct
export
bimap : {w1, w2, w1', w2' : p.world} ->
  (w1 ~> w1') -> (w2 ~> w2') -> (w1 ++ w2) ~> (w1' ++ w2')
bimap f g a x = case split x of
  Left  y => inl a (f a y)
  Right y => inr a (g a y)
