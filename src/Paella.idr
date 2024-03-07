module Paella

data A = P1 | P2 | P3


data World : Type where
  Lin : World
  (:<) : World -> A -> World

Ex1 : World
Ex1 = [< P2 , P3, P2]

data Var : A -> World -> Type where
  Here : Var a (w :< a)
  There : Var a w -> Var a (w :< b)

infixr 1 ~>

(~>) : World -> World -> Type
w1 ~> w2 = (a : A) -> Var a w1 -> Var a w2

-- (World, (~>)) is a category
idRen : w ~> w
idRen a x = x

(.) : w2 ~> w3 -> w1 ~> w2 -> w1 ~> w3
(.) f g a x = f a (g a x)

Family : Type
Family = World -> Type


record Closure (f : Family) (w : World) where
  constructor Close
  ctx : World
  weaken : ctx ~> w
  val : f ctx

infixr 1 -|>

-- Family transformation
(-|>) : (f, g : Family) -> Type
f -|> g = (w : World) -> f w -> g w

PresheafOver : Family -> Type
PresheafOver f = {w1, w2 : World}  -> (rho : w1 ~> w2) ->
  f w1 -> f w2


namespace Algebra
  public export
  D : Family -> Family
  D = Closure  --(b : World ** (b ~> a, f b))

  public export
  record DAlg (f : Family) where
    constructor MkDAlg
    eval : D f -|> f

  public export
  (.map) : {f : Family} -> DAlg f -> PresheafOver f
  alg.map {w1, w2} rho v = alg.eval w2 (Close w1 rho v)


namespace Coalgebra
  public export
  Nil : Family -> Family
  [] f a = (b : World) -> (a ~> b) -> f b

  public export
  record BoxCoalg (f : Family) where
    constructor MkBoxCoalg
    next : f -|> [] f

  public export
  (.map) : {f : Family} -> BoxCoalg f -> PresheafOver f
  coalg.map {w1,w2} rho v = coalg.next w1 v w2 rho

(++) : World -> World -> World
w1 ++ [<] = w1
w1 ++ (w2 :< a) = (w1 ++ w2) :< a

(.shift) : World -> Family -> Family
w1.shift f w2 = f (w1 ++ w2)

split : {w2 : World} -> Var a (w1 ++ w2) -> Either (Var a w1) (Var a w2)
split {w2 = [<]     } x = Left x
split {w2 = pos :< a} Here = Right Here
split {w2 = pos :< b} (There x) = bimap id (There) (split x)

inl : {w2 : World} -> w1 ~> w1 ++ w2
inl {w2 = [<]} a x = x
inl {w2 = w2 :< b} a x = There (inl a x)

inr : w2 ~> w1 ++ w2
inr {w2 = .(w2 :< a)} a Here = Here
inr {w2 = .(w2 :< b)} a (There x) = There (inr a x)

bimap : {w1, w2, w1', w2' : World} -> (w1 ~> w1') -> (w2 ~> w2') -> (w1 ++ w2) ~> (w1' ++ w2')
bimap f g a x = case split x of
  Left  y => inl a (f a y)
  Right y => inr a (g a y)

-- (f.shift) is actually a presheaf

(.shiftAlg) : (w1 : World) -> {f : Family} -> DAlg f -> DAlg (w1.shift f)
w1.shiftAlg {f} alg = MkDAlg $ \w, (Close ctx rho v) =>
  alg.map ?h2 v

test : String
test = "Hello from Idris2!"
