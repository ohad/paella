module Paella

import Data.DPair

import Data.SnocList
import Data.SnocList.Elem
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

  public export
  mapPropertyWithRelevant : {xs : List _} ->
    ((x : _) -> p x -> q x) -> All p xs -> All q xs
  mapPropertyWithRelevant f [] = []
  mapPropertyWithRelevant f (y :: ys) =
    f _ y :: mapPropertyWithRelevant f ys


namespace Data.SnocList.Quantifiers
  public export
  ForAny :  SnocList a -> (0 _ : (a -> Type)) -> Type
  ForAny sx p = Any p sx
  public export
  ForAll : SnocList a -> (0 p : (a -> Type)) -> Type
  ForAll sx p = All p sx

  public export
  injectAny : {xs : SnocList a} -> {p : a -> Type} -> x `Elem` xs -> p x -> Any p xs
  injectAny Here px = Here px
  injectAny (There y) px = There (injectAny y px)

  public export
  tabulate : (sx : SnocList a) -> ((x : a) -> p x) -> ForAll sx p
  tabulate [<] f = [<]
  tabulate (sx :< x) f = tabulate sx f :< f x

  public export
  tabulateElem : (xs : SnocList a) -> ((x : a) -> x `Elem` xs -> p x) -> ForAll xs p
  tabulateElem [<] f = [<]
  tabulateElem (sx :< x) f = tabulateElem sx (\y, pos => f y (There pos)) :< f x Here

  public export
  rippleAll : {0 xs : SnocList a} -> {0 f : a -> b} -> ForAll xs (p . f) -> ForAll (map f xs) p
  rippleAll [<] = [<]
  rippleAll (sx :< x) = rippleAll sx :< x

  public export
  rippleAny : {0 xs : SnocList a} -> {0 f : a -> b} -> ForAny xs (p . f) -> ForAny (map f xs) p
  rippleAny (Here x) = Here x
  rippleAny (There x) = There (rippleAny x)

  public export
  unrippleAll : {xs : SnocList a} -> {0 f : a -> b} -> ForAll (map f xs) p -> ForAll xs (p . f)
  unrippleAll sy with (xs)
    unrippleAll ([<]) | [<] = [<]
    unrippleAll (sy :< y) | (sx :< x) = unrippleAll sy :< y

  public export
  unrippleAny : {xs : SnocList a} -> {0 f : a -> b} -> ForAny (map f xs) p -> ForAny xs (p . f)
  unrippleAny {xs = [<]} _ impossible
  unrippleAny {xs = sx :< b} (Here  x  ) = Here x
  unrippleAny {xs = sx :< b} (There pos) = There (unrippleAny pos)

  public export
  applyAny : {xs : SnocList _} ->
    ((x : _) -> p x -> q x -> r x) -> All p xs -> Any q xs -> Any r xs
  applyAny f (sx :< x) (Here  u  ) = Here  (f _ x u)
  applyAny f (sx :< x) (There pos) = There (applyAny f sx pos)

  -- Putting these together results in a flexible version
  public export
  applyMapAllAny : {sx : SnocList a} ->
    ((x : a) -> (p . f) x -> (q . g) x -> r x) ->
    All p (map f sx) -> Any q (map g sx) -> Any r sx
  applyMapAllAny h su pos = applyAny h (unrippleAll su) (unrippleAny pos)

  public export
  zipPropertyWithRelevant : {xs : SnocList _} ->
    ((x : _) -> p x -> q x -> r x) -> All p xs -> All q xs -> All r xs
  zipPropertyWithRelevant f [<] vs = [<]
  zipPropertyWithRelevant f (u :< us) (v :< vs) = zipPropertyWithRelevant f u v :< f _ us vs

  public export
  mapPropertyWithRelevant : {xs : SnocList _} ->
    ((x : _) -> p x -> q x) -> All p xs -> All q xs
  mapPropertyWithRelevant f [<] = [<]
  mapPropertyWithRelevant f (sy :< y) = mapPropertyWithRelevant f sy :< f _ y



  public export
  mapAll : {sx : SnocList a} ->
    ((x : a) -> (p . f) x -> (q . g) x) ->
    All p (map f sx) -> All q (map g sx)
  mapAll h su = rippleAll $ mapPropertyWithRelevant h (unrippleAll su)

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
data A = ConsCell

||| A 0-th order context, operation's arities will be a
||| finite list of worlds.
World : Type
World = SnocList A

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

infixr 1 -|>, =|>, .:.

-- Family transformation
(-|>) : (f, g : Family) -> Type
f -|> g = (w : World) -> f w -> g w

-- Closed version
(.elem) : (f : Family) -> Type
f.elem = (w : World) -> f w


idFam : {f : Family} -> f -|> f
idFam w x = x

(.:.) : {f,g,h : Family} -> g -|> h -> f -|> g -> f -|> h
(beta .:. alpha) w = beta w . alpha w

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

{f : _} -> Cast (PresheafOver f) (BoxCoalg f) where
  cast psh = MkBoxCoalg $ \w, x, w', rho => psh rho x

{f : _} -> Cast (PresheafOver f) (DAlg f) where
  cast psh = MkDAlg $ \w, closure =>
    psh closure.weaken closure.val

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

||| Presheaf structure of product presheaf
BoxCoalgProd : {sf : SnocList Family} -> ForAll sf (\f => BoxCoalg f) ->
  BoxCoalg $ FamProd sf
BoxCoalgProd sbox = MkBoxCoalg $ \w, sx, w', rho =>
  zipPropertyWithRelevant (\f,box,x => box.map rho x)
    sbox
    sx

Env : World -> Family
Env w = (w ~>)

swap : FamProd [< f , g] -|> FamProd [< g, f]
swap w [< x , y] = [< y , x]

-- (f.shift) is actually an exponential
(.eval) : {w1 : World} -> {f : Family} -> (fPsh : DAlg f) ->
       FamProd [< w1.shift f, Env w1] -|> f
fPsh.eval w [< u, rho] = fPsh.map (cotuple rho idRen) u

(.curry) : {w1 : World} -> {f : Family} -> (fPsh : DAlg f) ->
  (FamProd [< f, Env w1] -|> g) -> f -|> w1.shift g
fPsh.curry alpha w u = alpha (w1 ++ w) [< fPsh.map inr u, inl]

(.curry') : {w1 : World} -> {f : Family} -> (fPsh : DAlg f) ->
  (FamProd [< Env w1, f] -|> g) -> f -|> w1.shift g
fPsh.curry' alpha w u = alpha (w1 ++ w) [< inl, fPsh.map inr u]

(.uncurry) : {w1 : World} -> {g : Family} -> (gPsh : DAlg g) ->
  (f -|> w1.shift g) -> (FamProd [< f, Env w1] -|> g)
gPsh.uncurry beta w [< u, rho] = gPsh.map (cotuple rho idRen) (beta w u)

-- General exponential of presheaves
infixr 2 -%

public export
(-%) : (f, g : Family) -> Family
(f -% g) w = (FamProd [< Env w, f]) -|> g

public export
eval : FamProd [< f -% g , f] -|> g
eval w [< alpha , x] = alpha w [< idRen, x]

public export
(.abst) : {gamma : Family} ->
  (PresheafOver gamma) -> (FamProd [< gamma , f ] -|> g) ->
  gamma -|> (f -% g)
psh.abst beta w env w2 [< rho , x] =
  beta w2 [< psh rho env , x]

-- Can derive from previous but can cut out hassle
public export
abst :
  (f -|> g) ->
  (f -% g).elem
abst f w w' [< rho , x] = f w' x

ExpCoalg : BoxCoalg (f -% g)
ExpCoalg = MkBoxCoalg $ \w, alpha, w', rho, w'', [< rho' , x] =>
  alpha w'' [< rho' . rho, x]

(.shiftIntoRepr) : {w0 : World} -> {g : Family} ->
  (PresheafOver g) ->
  ((Env w0) -% g) -|> (w0.shift g)
psh.shiftIntoRepr =
  (cast {from = BoxCoalg (Env w0 -% g)} $ ExpCoalg).curry
    {g, f = (Env w0) -% g} $ eval {f = Env w0, g = g}

(.shiftFromRepr) : {w0 : World} -> {g : Family} ->
  (PresheafOver g) ->
   (w0.shift g) -|> ((Env w0) -% g)
psh.shiftFromRepr =
  let coalg : BoxCoalg g = cast psh
      algeb = (cast {to = DAlg g} psh).eval
  in (w0.shiftCoalg coalg).map.abst algeb


record OpSig where
  constructor MkOpSig
  Args  : Family
  Arity : Family

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
  forgetAny $ applyMapAllAny
                (\w1,x,rho => fPsh.map (cotuple rho idRen) x)
                u
                rho

(.currySum) : {ws : SnocList World} -> {f : Family} -> (fPsh : DAlg f) ->
  (FamProd [< f, FamSum (map Env ws)] -|> g) -> f -|> g ^ ws
fPsh.currySum {ws = [<]} alpha w u = [<]
fPsh.currySum {ws = ws' :< w'} alpha w u =
  rippleAll (tabulateElem (ws' :< w')
  (\w1, pos => alpha (w1 ++ w) [< fPsh.map inr u, rippleAny {xs = ws' :< w'} {f = Env} (injectAny pos inl)]))

(.uncurrySum) : {ws : SnocList World} -> {g : Family} -> (gPsh : DAlg g) ->
  (f -|> g ^ ws) -> (FamProd [< f, FamSum (map Env ws)] -|> g)
gPsh.uncurrySum beta w [< u, rho] =
  forgetAny $ applyMapAllAny (\w1, x, rho' => gPsh.map (cotuple rho' idRen) x) (beta w u) rho

expMapSumRep : {ws : SnocList World} ->
  {f,g : Family} ->
  (f -|> g) -> (f ^ ws) -|> (g ^ ws)
expMapSumRep alpha w sx = mapAll (\x, y => alpha (x ++ w) y) sx

expMap :
  {f,g,e : Family} ->
  (f -|> g) -> (e -% f) -|> (e -% g)
expMap {f,g,e} alpha = ExpCoalg .map.abst (alpha .:. eval)

data (.Free) : Signature -> Family -> Family where
  Return : f -|> sig.Free f
  Op : {op : OpSig} ->
    {f : Family} ->
    op `Elem` sig ->
    -- Argument
    FamProd [< op.Args , op.Arity -% sig.Free f]
    -|> sig.Free f

record FunctorialOpSig (op : OpSig) where
  constructor MkFunOpSig
  Args  : PresheafOver op.Args
  Arity : PresheafOver op.Arity

FunctorialSignature : Signature -> Type
FunctorialSignature sig = ForAll sig $ FunctorialOpSig

BoxCoalgFree : {sig : Signature} -> {f : Family} ->
  FunctorialSignature sig ->
  BoxCoalg f -> BoxCoalg (sig.Free f)
BoxCoalgFree sigFunc coalg = MkBoxCoalg $ \w, term, w', rho =>
  case term of
    Return w1 var => Return w' (coalg.map rho var)
    Op pos w [< arg , cont] =>
      Op pos w'
        [< (indexAll pos sigFunc).Args rho arg
        , ExpCoalg .map rho cont]

-- Huh. Didn't need the Arity's functorial action here

(.AlgebraOver) : Signature -> Family -> Type
sig.AlgebraOver f = ForAll sig $ \op =>
  (op.Arity -% f) -|> (op.Args -% f)

MkAlgebraOver : {sig : Signature} -> {f : Family} ->
  (ForAll sig $ \op =>
    (FamProd [< op.Arity -% f , op.Args] -|> f))
  -> sig.AlgebraOver f
MkAlgebraOver = mapPropertyWithRelevant
  (\x => ExpCoalg .map.abst)




curryOp : (sig : Signature) ->
  (f : Family) -> (BoxCoalg f) ->
  (op : OpSig) -> op `Elem` sig ->
  op.Arity -% (sig.Free f) -|> (op.Args) -% (sig.Free f)
curryOp sig f coalg op pos =
  (ExpCoalg .map).abst (Op pos .:. swap)

TermAlgebra : {sig : Signature} ->
  (f : Family) -> (BoxCoalg f) -> sig.AlgebraOver (sig.Free f)
TermAlgebra {sig} f coalg = tabulateElem sig $
  curryOp sig f coalg

pure : {sig : Signature} -> {f : Family} -> f -|> sig.Free f
pure = Return

(.fold) : {sig : Signature} -> {f,g : Family} ->
  sig.AlgebraOver g ->
  (f -|> g) ->
  sig.Free f -|> g
a.fold env w (Return w x  ) = env w x
a.fold env w (Op {op} pos .(w) [< arg, k]) =
  let fold = a.fold env
      g_op = indexAll pos a w
      folded = g_op (expMap {e = op.Arity} fold w k)
  in eval w [< folded, arg]

(.extend) :  {sig : Signature} -> {f,g : Family} -> BoxCoalg g ->
  (f -|> sig.Free g) -> (sig.Free f -|> sig.Free g)
gPsh.extend alpha = (TermAlgebra g gPsh).fold alpha

(.join) : {sig : Signature} -> {f : Family} -> BoxCoalg f ->
  sig.Free (sig.Free f) -|> sig.Free f
fPsh.join = fPsh.extend idFam

-- Postulate: each parameter has a type
-- For now, just cons cells
TypeOf : A -> Family
TypeOf ConsCell =
  Maybe . (FamProd [< const String, Var ConsCell])

||| Type of reading an A-cell
readType : A -> OpSig
readType a = MkOpSig
  { Args = Var a
  , Arity = TypeOf a
  }

||| Type of writing an a
||| w_0 : [a, []]
writeType : A -> OpSig
writeType a = MkOpSig
  { Args = FamProd [< Var a, TypeOf a]
  , Arity = const ()
  }


||| Allocate a fresh cell storing an a value
newType : A -> OpSig
newType a = MkOpSig
  { Args = [< a].shift (TypeOf a)
  , Arity = Var a
  }

LSSig : Signature
LSSig = [
  readType ConsCell,
  writeType ConsCell,
  newType ConsCell
]

Heaplet : (shape : World) -> Family
Heaplet shape = FamProd (map TypeOf shape)

infix 3 !! , ::=

(!!) : Heaplet shape w -> Var a shape ->
  TypeOf a w
(h :< x) !! Here = x
[<]      !! (There pos) impossible
(h :< x) !! (There pos) = h !! pos

record Update (a : A) (shape, w : World) where
  constructor (::=)
  loc : Var a shape
  val : TypeOf a w

(.update) : Heaplet shape w -> Update a shape w -> Heaplet shape w
(h :< old).update (Here ::= new) = (h :< new)
[<].update (There pos ::= v) impossible
(h :< x).update (There pos ::= v) = h.update (pos ::= v) :< x

TypeOfFunctoriality : (a : A) -> PresheafOver $ TypeOf a
-- Should propagate structure more nicely
TypeOfFunctoriality ConsCell rho Nothing = Nothing
TypeOfFunctoriality ConsCell rho (Just [< str , loc]) =
  Just [< str , rho _ loc]

HeapletCoalg : {shape : World} -> BoxCoalg (Heaplet shape)
HeapletCoalg = MkBoxCoalg $ \w, heaplet,w',rho =>
  mapAll
    (\a => TypeOfFunctoriality a rho)
    heaplet

Heap : Family
Heap w = Heaplet w w

Ex1 : Heap [< ConsCell, ConsCell, ConsCell]
Ex1 = [< Just [< "first of singleton", There Here]
      ,  Nothing
      ,  Just [< "loop" , Here]
      ]

extendHeap : {w : World} ->
  FamProd [< Heap , w.shift $ Heaplet w ] -|> w.shift Heap
extendHeap {w} w' [< heap , init] =
  let u = unrippleAll $ (HeapletCoalg {shape = w'}).map
           (inr {w1 = w}) heap
      v = unrippleAll init
     -- Probably terrible performance, but meh
  in rippleAll (v ++ u)

record Private (f : Family) (w : World) where
  constructor Hide
  ctx : World
  val : f (ctx ++ w)

namespace Private
  public export
  pure : {f : Family} -> f -|> Private f
  pure w x = Hide {ctx = [<], val =
    replace {p = f}
      -- I'm going to regret this...
      (sym $ appendLinLeftNeutral w)
      x
      }

{- The local independent coproduct completes a span of maps:
        rho2                   rho2
     w0 ---> w2            w0 ---> w2
 rho1|            =>  rho1 |       | rho1'
     v                     v       V
     w1                    w1 ---> w3
                              rho2'
   in an independent way. The result is indeed a pushout,
   and in fact a pullback too, but that's not the correct
   universal property to work off of.

   Let the square be rho : w0 -> w3

   The calculation becomes more complicated because rho2
   and rho1 may identify different elements of w0:

   rho1 x = rho1 y
   rho2 x = rho2 z

   and therefore the square must equate y and z:
   rho y = rho x = rho z

   The calculation is, in general, expensive, but
   if we know that, say, rho1 is an injection, e.g.:

   rho1 : w0 -> w ++ w0

   then it is easier to calculate:
           rho2
        w0 ---> w2
    inl |       | inr
        v       V
      w+w0 ---> w + w2
        w + rho2
-}

PrivateCoal : {f : Family} ->
  (coalg : BoxCoalg f) -> BoxCoalg (Private f)
PrivateCoal coalg = MkBoxCoalg $ \w, hidden, w', rho => Hide
  { ctx = hidden.ctx
  , val = coalg.map (Paella.bimap idRen rho) hidden.val
  }

-- We can hide locations
hide : {w1,w : World} -> {f : Family} ->
  Private f (w1 ++ w) -> Private f w
hide hidden =
  Hide
    { ctx = hidden.ctx ++ w1
    , val = replace {p = f}
              (appendAssociative (hidden.ctx) w1 w)
              hidden.val
    }

LSHandlerCarrier : (f : Family) -> Family
LSHandlerCarrier f = Heap -% Private f

LSHandlerPsh : (coalg : BoxCoalg f) ->
  BoxCoalg $ LSHandlerCarrier f
LSHandlerPsh coalg = ExpCoalg

val : {f : Family} -> {coalg : BoxCoalg f} ->
  coalg =|> (LSHandlerPsh coalg)
val = coalg.map.abst $ \w, [< v, heap] =>
  Private.pure {f} w v

-- Heap's LSAlgebra structure
LSalg : {f : Family} -> {coalg : BoxCoalg f} ->
  LSSig .AlgebraOver (LSHandlerCarrier f)
LSalg = MkAlgebraOver
  [ -- readType
     \roots, [< kont, loc], shape, [< rho, heap] =>
       let result = heap !! (rho _ loc)
       in eval shape [< kont shape [< rho , result] , heap]
  , -- writeType
    \roots, [< kont, [<loc, newval]], shape, [< rho, heap] =>
       let newHeap = heap.update
                     (rho _ loc ::=
                        TypeOfFunctoriality ConsCell rho newval)
       in eval shape [< kont shape [< rho , ()] , newHeap]
  , -- new
    \roots, [< kont, newval], shape, [< rho, heap] =>
      let newheap : Heap ([< ConsCell] ++ shape)
                  := extendHeap {w = [< ConsCell]} shape
                     [< heap , [<
                       TypeOfFunctoriality ConsCell
                         (Paella.bimap idRen rho)
                       newval
                     ]]
          newloc : Var ConsCell $ [< ConsCell] ++ shape
                 := inl _ Here
          -- Calculate the result without hiding the new
          -- location
          result : Private f ([<ConsCell] ++ shape)
                 := kont ([< ConsCell] ++ shape)
                          [< inr . rho , newloc]
                          ([< ConsCell] ++ shape)
                          ([< idRen, newheap])
      in hide result
  ]

{-
example : {f : Family} -> {auto fPsh : BoxCoalg f} -> (w : World) ->
  Env [< P] w -> LSFreeMonad f w -> LSFreeMonad f w
example w env k = read w [< k, env, k]

test : String
test = "Hello from Idris2!"
-}
