module Paella

import Data.DPair

import Data.SnocList
import Data.SnocList.Quantifiers

import Data.List
import Data.List.Elem
import Data.List.Quantifiers

namespace Data.List.Quantifiers
  public export
  ForAny :  List a -> (0 _ : (a -> Type)) -> Type
  ForAny xs p = Any p xs
  public export
  ForAll :  List a -> (0 _ : (a -> Type)) -> Type
  ForAll xs p = All p xs

  public export
  tabulate : (sx : List a) -> ((x : a) -> p x) -> ForAll sx p
  tabulate [] f = []
  tabulate (x :: xs) f = f x :: tabulate xs f

  public export
  tabulateElem : (xs : List a) -> ((x : a) -> x `Elem` xs -> p x) -> ForAll xs p
  tabulateElem [] f = []
  tabulateElem (x :: xs) f =
    f x Here :: tabulateElem xs (\y, pos => f y (There pos))

namespace Data.SnocList.Quantifiers
  public export
  ForAny :  SnocList a -> (0 _ : (a -> Type)) -> Type
  ForAny sx p = Any p sx
  public export
  ForAll : SnocList a -> (0 p : (a -> Type)) -> Type
  ForAll sx p = All p sx

  public export
  tabulate : (sx : SnocList a) -> ((x : a) -> p x) -> ForAll sx p
  tabulate [<] f = [<]
  tabulate (sx :< x) f = tabulate sx f :< f x

  public export
  rippleAll : {0 xs : SnocList a} -> ForAll xs (p . f) -> ForAll (map f xs) p
  rippleAll [<] = [<]
  rippleAll (sx :< x) = rippleAll sx :< x

  public export
  unrippleAll : {xs : SnocList a} -> {f : a -> b} -> ForAll (map f xs) p -> ForAll xs (p . f)
  unrippleAll sy with (xs)
    unrippleAll ([<]) | [<] = [<]
    unrippleAll (sy :< y) | (sx :< x) = unrippleAll sy :< y

  public export
  unrippleAny : {xs : SnocList a} -> {f : a -> b} -> ForAny (map f xs) p -> ForAny xs (p . f)
  unrippleAny {xs = [<]} _ impossible
  unrippleAny {xs = sx :< b} (Here  x  ) = Here x
  unrippleAny {xs = sx :< b} (There pos) = There (unrippleAny pos)

  public export
  applyAny : {xs : SnocList _} ->
    ((x : _) -> p x -> q x -> r x) -> All p xs -> Any q xs -> Any r xs
  applyAny f (sx :< x) (Here  u  ) = Here  (f _ x u)
  applyAny f (sx :< x) (There pos) = There (applyAny f sx pos)

  -- For completeness

  public export
  applyAnyErased : {0 xs : SnocList _} ->
    ((0 x : _) -> p x -> q x -> r x) -> All p xs -> Any q xs -> Any r xs
  applyAnyErased f (sx :< x) (Here  u  ) = Here  (f _ x u)
  applyAnyErased f (sx :< x) (There pos) = There (applyAnyErased f sx pos)

  public export
  forgetAny : {0 sx : SnocList a} -> Any (const type) sx -> type
  forgetAny pos = (toExists pos).snd

||| The type of available parameter types
||| In the final development, we will abstract/parameterise over this type
data A = P1 | P2 | P3

||| A 0-th order context, operation's arities will be a
||| finite list of worlds.
World : Type
World = SnocList A

Ex1 : World
Ex1 = [< P2 , P3, P2]

||| A `x : Var a w` is a first-order variable of paramter type `a` in `w`
data Var : A -> World -> Type where
  Here : Var a (w :< a)
  There : Var a w -> Var a (w :< b)

infixr 1 ~>

||| A renaming from src to tgt, sending each variable in src to a
||| variable in tgt
(~>) : (src, tgt : World) -> Type
w1 ~> w2 = (a : A) -> Var a w1 -> Var a w2

-- (World, (~>)) is a category
idRen : w ~> w
idRen a x = x

(.) : w2 ~> w3 -> w1 ~> w2 -> w1 ~> w3
(.) f g a x = f a (g a x)

Family : Type
Family = World -> Type

infixr 1 -|>, =|>

-- Family transformation
(-|>) : (f, g : Family) -> Type
f -|> g = (w : World) -> f w -> g w

PresheafOver : Family -> Type
PresheafOver f = {w1, w2 : World} -> (rho : w1 ~> w2) ->
  f w1 -> f w2

namespace Algebra
  ||| A presheaf structure given in coend form
  public export
  record Closure (f : Family) (w : World) where
    constructor Close
    ctx : World
    weaken : ctx ~> w
    val : f ctx

  ||| The left-adjoint Fiore-transform monad (Diamond)
  public export
  D : Family -> Family
  D = Closure  --(b : World ** (b ~> a, f b))

  ||| Fiore transform: a DAlg (with laws) is equivalent to a presheaf
  ||| (with laws)
  public export
  record DAlg (f : Family) where
    constructor MkDAlg
    eval : D f -|> f

  public export
  (.map) : {f : Family} -> DAlg f -> PresheafOver f
  alg.map {w1, w2} rho v = alg.eval w2 (Close w1 rho v)

  public export
  (=|>) : {f,g : Family} -> (fAlg : DAlg f) -> (gAlg : DAlg g) -> Type
  (=|>) {f,g} _ _ = f -|> g

namespace Coalgebra
  ||| A presheaf structure given in end form
  ||| The right-adjoint Fiore-transform comonad (Box)
  public export
  Nil : Family -> Family
  [] f a = (b : World) -> (a ~> b) -> f b

  ||| Fiore transform: a BoxCoalg (with laws) is equivalent to a
  ||| presheaf (with laws)
  public export
  record BoxCoalg (f : Family) where
    constructor MkBoxCoalg
    next : f -|> [] f

  public export
  (.map) : {f : Family} -> BoxCoalg f -> PresheafOver f
  coalg.map {w1,w2} rho v = coalg.next w1 v w2 rho

  public export
  (=|>) : {f,g : Family} -> (fAlg : BoxCoalg f) -> (gAlg : BoxCoalg g) -> Type
  (=|>) {f,g} _ _ = f -|> g

{f : _} -> Cast (DAlg f) (BoxCoalg f) where
  cast alg = MkBoxCoalg $ \w, x, w', rho => alg.map rho x

{f : _} -> Cast (BoxCoalg f) (DAlg f) where
  cast coalg = MkDAlg $ \w, closure => coalg.map closure.weaken closure.val

||| Fiore-transform of presheaf exponentiation: f^(Yoneda w1).
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

cotuple : {w2 : World} -> (w1 ~> w) -> (w2 ~> w) -> w1 ++ w2 ~> w
cotuple {w2 = [<]    } f g   a  x        = f a x
cotuple {w2 = w2 :< b} f g .(b) Here     = g b Here
cotuple {w2 = w2 :< b} f g   a (There x) = cotuple f (\c, y => g c (There y)) a x

||| Monoidal action on maps
bimap : {w1, w2, w1', w2' : World} -> (w1 ~> w1') -> (w2 ~> w2') -> (w1 ++ w2) ~> (w1' ++ w2')
bimap f g a x = case split x of
  Left  y => inl a (f a y)
  Right y => inr a (g a y)

-- (f.shift) is actually a presheaf
(.shiftAlg) : (w1 : World) -> {f : Family} -> DAlg f -> DAlg (w1.shift f)
w1.shiftAlg {f} alg = MkDAlg $ \w, (Close ctx rho v) =>
  alg.map (Paella.bimap idRen rho) v

(.shiftCoalg) : (w1 : World) -> {f : Family} -> BoxCoalg f -> BoxCoalg (w1.shift f)
w1.shiftCoalg {f} boxCoalg = cast (w1.shiftAlg $ cast {to = DAlg f} boxCoalg)

||| The product family is given pointwise
FamProd : SnocList Family -> Family
FamProd sf w = ForAll sf $ \f => f w

Ex2 : Family
Ex2 = FamProd [< Var P1 , Var P2 , Var P3 ]

Ex21 : Ex2 [< P3, P2, P1, P2, P3]
Ex21 = let w : World
           w = [< P3, P2, P1, P2, P3]
           x : Var P3 w
           x = Here
           y : Var P2 w
           y = There Here
           z : Var P1 w
           z = There $ There Here
           u : Var P2 w
           u = There $ There $ There Here
           v : Var P3 w
           v = There $ There $ There $ There Here
       in [< z , y , v]

zipPropertyWithRelevant : {xs : SnocList _} ->
  ((x : _) -> p x -> q x -> r x) -> All p xs -> All q xs -> All r xs
zipPropertyWithRelevant f [<] vs = [<]
zipPropertyWithRelevant f (u :< us) (v :< vs) = zipPropertyWithRelevant f u v :< f _ us vs

||| Presheaf structure of product presheaf
BoxCoalgProd : {sf : SnocList Family} -> ForAll sf (\f => BoxCoalg f) ->
  BoxCoalg $ FamProd sf
BoxCoalgProd sbox = MkBoxCoalg $ \w, sx, w', rho =>
  zipPropertyWithRelevant (\f,box,x => box.map rho x)
    sbox
    sx

Env : World -> Family
Env w = (w ~>)


-- (f.shift) is actually an exponential
(.eval) : {w1 : World} -> {f : Family} -> (fPsh : DAlg f) ->
       FamProd [< w1.shift f, Env w1] -|> f
fPsh.eval w [< u, rho] = fPsh.map (cotuple rho idRen) u

(.curry) : {w1 : World} -> {f : Family} -> (fPsh : DAlg f) ->
  (FamProd [< f, Env w1] -|> g) -> f -|> w1.shift g
fPsh.curry alpha w u = alpha (w1 ++ w) [< fPsh.map inr u , inl]

(.uncurry) : {w1 : World} -> {g : Family} -> (gPsh : DAlg g) ->
  (f -|> w1.shift g) -> (FamProd [< f, Env w1] -|> g)
gPsh.uncurry beta w [< u, rho] = gPsh.map (cotuple rho idRen) (beta w u)

record OpSig where
  constructor MkOpSig
  Args  : World
  Arity : SnocList World

forkType : OpSig
forkType = MkOpSig
  { Args = [<]
  , Arity = [< [< P1], [<]]
  }

Signature : Type
Signature = List OpSig

infixl 7 ^

||| The exponentiation of f by the sum of representables coprod_{w in ws} y(w)
(^) : Family -> SnocList World -> Family
f ^ ws = FamProd (map (\w => w.shift f) ws)

ArityExponential : {f : Family} -> (BoxCoalg f) ->
  {ws : SnocList World} -> BoxCoalg (f ^ ws)
ArityExponential {f, ws} boxCoalg
  = BoxCoalgProd $ rippleAll $ tabulate _
                 $ \w => w.shiftCoalg boxCoalg

||| The sum family is given pointwise
FamSum : SnocList Family -> Family
FamSum sf w = ForAny sf $ \f => f w

||| Presheaf structure of sum presheaf
BoxCoalgSum : {sf : SnocList Family} -> ForAll sf (\f => BoxCoalg f) ->
  BoxCoalg $ FamSum sf
BoxCoalgSum salg =  MkBoxCoalg $ \w, sx, w', rho => applyAny (\f, coalg => coalg.map rho) salg sx

-- (f ^ ws) is actually an exponential
(.evalSum) : {ws : SnocList World} -> {f : Family} -> (fPsh : DAlg f) ->
       FamProd [< f ^ ws, FamSum (map Env ws)] -|> f
fPsh.evalSum w [< u, rho] =
  let (u', rho') = (unrippleAll u, unrippleAny rho)
  in forgetAny $ applyAny (\w1,x,rho => fPsh.map (cotuple rho idRen) x) u' rho'

data (.Free) : Signature -> Family -> Family where
  Return : f -|> sig.Free f
  Op : {op : OpSig} ->
    {w : World} ->
    {f : Family} ->
    op `Elem` sig ->
    -- Argument
    Env op.Args w ->
    -- Continuation
    ((sig.Free f) ^ op.Arity) w ->
    sig.Free f w

(.AlgebraOver) : Signature -> Family -> Type
sig.AlgebraOver f = ForAll sig $ \op =>
  f ^ op.Arity -|> (op.Args).shift f



TermAlgebra : (sig : Signature) -> (f : Family) -> sig.AlgebraOver (sig.Free f)
TermAlgebra sig f = tabulateElem sig $ \op,pos,w,env =>
  let shed = Op pos ?TermAlgebra_rhs ?h189
  in ?result

{-
DAlgProd : {sf : SnocList Family} -> ForAll sf (\f => DAlg f) ->
  DAlg $ FamProd sf
DAlgProd salg = MkDAlg $ \w, closure => ?h89
-}
  {-zipPropertyWith
  (\x => ?DAlgProd_rhs_2)
  salg
  ?DAlgProd_rhs_4-}

test : String
test = "Hello from Idris2!"
