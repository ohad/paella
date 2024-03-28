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

  public export
  splitAll : {sy, sx : SnocList _} ->
    All p (sy ++ sx) -> (All p sy, All p sx)
  splitAll {sx = [<]} sa = (sa, [<])
  splitAll {sx = _ :< _} (sa :< a) =
    let (sb, sa') = splitAll sa in (sb, sa' :< a)
  
  public export
  joinAll : {sy, sx : SnocList _} ->
    All p sy -> All p sx -> All p (sy ++ sx)
  joinAll {sx = [<]} sa [<] = sa
  joinAll {sx = _ :< _} sa (sb :< b) = joinAll sa sb :< b

||| The type of available parameter types
||| In the final development, we will abstract/parameterise over this type
data A = P

||| A 0-th order context, operation's arities will be a
||| finite list of worlds.
World : Type
World = SnocList A

||| A `x : Var a w` is a first-order variable of paramter type `a` in `w`
data Var : A -> World -> Type where
  Here : Var a (w :< a)
  There : Var a w -> Var a (w :< b)

Eq (Var a w) where
  Here      == Here      = True
  (There x) == (There y) = x == y
  _         == _         = False

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

idFam : {f : Family} -> f -|> f
idFam w x = x

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

untuple : {w2 : World} -> (w1 ++ w2 ~> w) -> Pair (w1 ~> w) (w2 ~> w)
untuple f = (f . inl, f . inr)

idLeft : {w : World} -> [< ] ++ w ~> w
idLeft {w = [<]} a x = x
idLeft {w = w :< b} b Here = Here
idLeft {w = w :< b} a (There pos) = There (idLeft a pos)

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

record OpSig where
  constructor MkOpSig
  Args  : World
  Arity : SnocList World

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

expMap : {ws : SnocList World} ->
  {f,g : Family} ->
  (f -|> g) -> (f ^ ws) -|> (g ^ ws)
expMap alpha w sx = mapAll (\x, y => alpha (x ++ w) y) sx

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

BoxCoalgFree : {sig : Signature} -> {f : Family} -> BoxCoalg f -> BoxCoalg (sig.Free f)
BoxCoalgFree coalg = MkBoxCoalg $ \w, term, w', rho =>
  case term of
    Return w1 var => Return w' (coalg.map rho var)
    Op pos arg cont =>
      let freeCoalg = BoxCoalgFree {sig = sig} {f = f} coalg
          recurse = (\x => freeCoalg.map (bimap idRen {w1 = x} {w1' = x} rho))
      in Op pos (rho . arg) (rippleAll (mapPropertyWithRelevant recurse (unrippleAll cont)))

(.AlgebraOver) : Signature -> Family -> Type
sig.AlgebraOver f = ForAll sig $ \op =>
  f ^ op.Arity -|> (op.Args).shift f

curryOp : (sig : Signature) -> (f : Family) -> (BoxCoalg f) ->
  (op : OpSig) -> op `Elem` sig ->
  (sig.Free f) ^ op.Arity -|> (op.Args).shift (sig.Free f)
curryOp sig f coalg op pos =
  let freeCoalg = (BoxCoalgFree coalg)
      expAlg = cast {to = DAlg (sig.Free f ^ op.Arity)}
             $ ArityExponential {ws = op.Arity, f = sig.Free f} freeCoalg
  in expAlg.curry' (\w, [< rho, u] => Op {w = w} pos rho u)

TermAlgebra : (sig : Signature) -> (f : Family) -> (BoxCoalg f) -> sig.AlgebraOver (sig.Free f)
TermAlgebra sig f coalg = tabulateElem sig $ curryOp sig f coalg

pure : {sig : Signature} -> {f : Family} -> f -|> sig.Free f
pure = Return

(.fold) : {sig : Signature} -> {f,g : Family} ->
  sig.AlgebraOver g ->
  BoxCoalg g ->
  (f -|> g) ->
  sig.Free f -|> g
a.fold gPsh env w (Return w x  ) = env w x
a.fold gPsh env w (Op {op = op} pos arg k) =
  let fold = a.fold gPsh env
      g_op = indexAll pos a w
      folded = g_op (expMap {ws = op.Arity} fold w k)
  in (cast {to = DAlg g} gPsh).eval w [< folded, arg]

(.extend) :  {sig : Signature} -> {f,g : Family} -> BoxCoalg g ->
  (f -|> sig.Free g) -> (sig.Free f -|> sig.Free g)
gPsh.extend alpha =
  let alg = TermAlgebra sig g gPsh
      freePsh = BoxCoalgFree gPsh
  in alg.fold freePsh alpha

(.join) : {sig : Signature} -> {f : Family} -> BoxCoalg f ->
  sig.Free (sig.Free f) -|> sig.Free f
fPsh.join = fPsh.extend idFam

||| Type of reading a bit:
||| ? : [[], a, []]
ReadType : OpSig
ReadType = MkOpSig
  { Args = [< P]
  , Arity = [< [<], [<]]
  }

||| Type of writing a 0:
||| w_0 : [a, []]
Write0Type : OpSig
Write0Type = MkOpSig
  { Args = [< P]
  , Arity = [< [<]]
  }

||| Type of writing a 1:
||| w_1 : [a, []]
Write1Type : OpSig
Write1Type = MkOpSig
  { Args = [< P]
  , Arity = [< [<]]
  }

||| Type of equality testing:
||| ?_= : [[], a, a, []]
EqualTestType : OpSig
EqualTestType = MkOpSig
  { Args = [< P, P]
  , Arity = [< [<], [<]]
  }

||| Type of restriction (new) to 0:
||| nu_0 : [[a]]
Restrict0Type : OpSig
Restrict0Type = MkOpSig
  { Args = [< ]
  , Arity = [< [< P]]
  }

||| Type of restriction (new) to 1:
||| nu_1 : [[a]]
Restrict1Type : OpSig
Restrict1Type = MkOpSig
  { Args = [< ]
  , Arity = [< [< P]]
  }

LSSig : Signature
LSSig = [
  ReadType,
  Write0Type,
  Write1Type,
  EqualTestType,
  Restrict0Type,
  Restrict1Type
]

readOpIndex : ReadType `Elem` LSSig
readOpIndex = Here

write0OpIndex : Write0Type `Elem` LSSig
write0OpIndex = There Here

write1OpIndex : Write1Type `Elem` LSSig
write1OpIndex = There $ There Here

equalTestOpIndex : EqualTestType `Elem` LSSig
equalTestOpIndex = There $ There $ There Here

restrict0OpIndex : Restrict0Type `Elem` LSSig
restrict0OpIndex = There $ There $ There $ There Here

restrict1OpIndex : Restrict1Type `Elem` LSSig
restrict1OpIndex = There $ There $ There $ There $ There Here

LSAlgebra : (f : Family) -> Type
LSAlgebra = LSSig .AlgebraOver

LSFreeMonad : (f : Family) -> Family
LSFreeMonad = LSSig .Free

LSTermAlgebra : (f : Family) -> (BoxCoalg f) -> LSAlgebra (LSFreeMonad f)
LSTermAlgebra f fPsh = TermAlgebra LSSig f fPsh

read : {f : Family} -> {auto fPsh : BoxCoalg f} ->
  FamProd [< LSFreeMonad f, Env [< P], LSFreeMonad f] -|> LSFreeMonad f
read w [< k0, p, k1] =
  let alg = LSTermAlgebra f fPsh
      freePsh = cast
        {to = DAlg (LSFreeMonad f)}
        (BoxCoalgFree {sig = LSSig} fPsh)
      op = indexAll readOpIndex alg
  in freePsh.uncurry op w [< [< freePsh.map inr k0, freePsh.map inr k1], p]

write : {f : Family} -> {auto fPsh : BoxCoalg f} -> Bool ->
  FamProd [< Env [< P], LSFreeMonad f] -|> LSFreeMonad f
write bit w [< p, k] =
  let alg = LSTermAlgebra f fPsh
      freePsh = cast
        {to = DAlg (LSFreeMonad f)}
        (BoxCoalgFree {sig = LSSig} fPsh)
      -- Don't know how to move the if up (probably need to set some implicits)
      op0 = indexAll write0OpIndex alg
      impl0 = freePsh.uncurry op0 w [< [< freePsh.map inr k], p]
      op1 = indexAll write1OpIndex alg
      impl1 = freePsh.uncurry op1 w [< [< freePsh.map inr k], p]
  in if bit then impl1 else impl0

equal : {f : Family} -> {auto fPsh : BoxCoalg f} ->
  FamProd [< LSFreeMonad f, Env [< P], Env [< P], LSFreeMonad f] -|>
  LSFreeMonad f
equal w [< k0, p, q, k1] =
  let alg = LSTermAlgebra f fPsh
      freePsh = cast
        {to = DAlg (LSFreeMonad f)}
        (BoxCoalgFree {sig = LSSig} fPsh)
      op = indexAll equalTestOpIndex alg
      -- I think this is the correct thing to do
      pq = cotuple p q
  in freePsh.uncurry op w [< [< freePsh.map inr k0, freePsh.map inr k1], pq]

new : {f : Family} -> {auto fPsh : BoxCoalg f} -> Bool ->
  [< P].shift (LSFreeMonad f) -|> LSFreeMonad f
new bit w k =
  let alg = LSTermAlgebra f fPsh
      freePsh = cast
        {to = DAlg (LSFreeMonad f)}
        (BoxCoalgFree {sig = LSSig} fPsh)
      -- Same issue as above
      op0 = indexAll restrict0OpIndex alg
      impl0 = freePsh.uncurry op0 w [< [< k], inr]
      op1 = indexAll restrict1OpIndex alg
      impl1 = freePsh.uncurry op1 w [< [< k], inr]
  in if bit then impl1 else impl0

TypeOf : A -> Type
TypeOf P = Bool

StateIn : Family
StateIn w = ForAll w TypeOf

getComponent : Var a w -> StateIn w -> TypeOf a
getComponent Here (_ :< s) = s
getComponent (There pos) (ss :< _) = getComponent pos ss

setComponent : Var a w -> StateIn w -> TypeOf a -> StateIn w
setComponent Here (ss :< _) s' = ss :< s'
setComponent (There pos) (ss :< s) s' = setComponent pos ss s' :< s

-- Viewed as in Inj-presheaf, free Inj-LS algebra on the presheaf which is
-- constantly t
Heap : Type -> Family
Heap t w = StateIn w -> Pair t (StateIn w)

pureHeap : t -> Heap t w
pureHeap t = \x => (t, x)

runHeap : Heap t w -> StateIn w -> Pair t (StateIn w)
runHeap h ss = h ss

-- Heap operations
readHeapOp : FamProd [< Heap t, Env [< P], Heap t] -|> Heap t
readHeapOp w [< k0, p, k1] ss =
  let sp = getComponent (p _ Here) ss in
  if sp then k0 ss else k1 ss

writeHeapOp : Bool -> FamProd [< Env [< P], Heap t] -|> Heap t
writeHeapOp b w [< p, k] ss =
  let (t, ss') = k ss in
  (t, setComponent (p _ Here) ss' b)

newHeapOp : Bool -> [< P].shift (Heap t) -|> Heap t
newHeapOp b w k ss =
  let combined = joinAll {sy = [< P]} [< b] ss
      (t, ss') = k combined
  in (t, snd (splitAll {sy = [<P]} ss'))

-- The action of the injection n -> n + 1 of Inj on the heap
extendHeap : Heap t -|> [< P].shift (Heap t)
extendHeap w h sv =
  let (v', sv') = splitAll {sy = [< P]} sv
      (x, sv'') = h sv'
  in (x, joinAll v' sv')

-- Viewed as the right Kan extension of Heap along the inclusion Inj -> Fin
LocHeap : Type -> Family
LocHeap t w = (w' : World) -> (w ~> w') -> Heap t w'

runLocHeap : (w' : World) -> (w ~> w') -> LocHeap t w ->
  StateIn w' -> Pair t (StateIn w')
runLocHeap w' rho h s = h w' rho s

-- LocHeap is a presheaf
LocHeapCoalg : {t : Type} -> BoxCoalg (LocHeap t)
LocHeapCoalg = MkBoxCoalg $ \w, h, w'', rho => \w', rho' => h w' (rho' . rho)

LocHeapAlg : {t : Type} -> DAlg (LocHeap t)
LocHeapAlg = cast {from = BoxCoalg (LocHeap t)} LocHeapCoalg

readLocHeapOp : FamProd [< LocHeap t, Env [< P], LocHeap t] -|> LocHeap t
readLocHeapOp w [< k0, p, k1] w' rho =
  let k0' = k0 w' rho
      k1' = k1 w' rho
      p' = rho . p
  in readHeapOp w' [< k0', p', k1']

writeLocHeapOp : Bool -> FamProd [< Env [< P], LocHeap t] -|> LocHeap t
writeLocHeapOp b w [< p, k] w' rho =
  let p' = rho . p
      k' = k w' rho
  in writeHeapOp b w' [< p', k']

newLocHeapOp : Bool -> [< P].shift (LocHeap t) -|> LocHeap t
newLocHeapOp b w k w' rho =
  let rho' = bimap {w1 = [< P], w1' = [< P]} idRen rho
      k' = k ([< P] ++ w') rho'
  in newHeapOp b w' k'

equalLocHeapOp :
  FamProd [< LocHeap t, Env [< P], Env [< P], LocHeap t] -|> LocHeap t
equalLocHeapOp w [< k0, p, q, k1] w' rho =
  let k0' = k0 w' rho
      k1' = k1 w' rho
      p' = (rho . p) _ Here
      q' = (rho . q) _ Here
  in if p' == q' then k0' else k1'

-- Faffing with currying

readLocHeapOp' : {t : Type} ->
  (LocHeap t) ^ ReadType .Arity -|> (ReadType .Args).shift (LocHeap t)
readLocHeapOp' =
  let op' : FamProd
              [< (LocHeap t) ^ ReadType .Arity
              ,  Env (ReadType .Args)
              ] -|> LocHeap t
      op' w [< [< k0, k1], p] = readLocHeapOp w
        [< LocHeapCoalg .map idLeft k0
        ,  p
        ,  LocHeapCoalg .map idLeft k1
        ]
      coalg : BoxCoalg ((LocHeap t) ^ ReadType .Arity)
      coalg = ArityExponential {ws = ReadType .Arity} LocHeapCoalg
  in (cast coalg).curry op'

writeLocHeapOp' : {t : Type} -> Bool ->
  (LocHeap t) ^ Write0Type .Arity -|> (Write0Type .Args).shift (LocHeap t)
writeLocHeapOp' b =
  let op' : FamProd
              [< (LocHeap t) ^ Write0Type .Arity
              ,  Env (Write0Type .Args)
              ] -|> LocHeap t
      op' w [< [< k], p] = writeLocHeapOp b w
        [< p
        ,  LocHeapCoalg .map idLeft k
        ]
      coalg : BoxCoalg ((LocHeap t) ^ Write0Type .Arity)
      coalg = ArityExponential {ws = Write0Type .Arity} LocHeapCoalg
  in (cast coalg).curry op'

newLocHeapOp' : {t : Type} -> Bool ->
  (LocHeap t) ^ Restrict0Type .Arity -|> (Restrict0Type .Args).shift (LocHeap t)
newLocHeapOp' b =
  let op' : FamProd
              [< (LocHeap t) ^ Restrict0Type .Arity
              ,  Env Restrict0Type .Args
              ] -|> LocHeap t
      op' w [< [< k], p] = newLocHeapOp b w k
      coalg : BoxCoalg ((LocHeap t) ^ Restrict0Type .Arity)
      coalg = ArityExponential {ws = Restrict0Type .Arity} LocHeapCoalg
  in (cast coalg).curry op'

equalLocHeapOp' : {t : Type} ->
  (LocHeap t) ^ EqualTestType .Arity -|> (EqualTestType .Args).shift (LocHeap t)
equalLocHeapOp' =
  let op' : FamProd
              [< (LocHeap t) ^ EqualTestType .Arity
    ,            Env (EqualTestType .Args)
              ] -|> LocHeap t
      op' w [< [< k0, k1], pq] =
        let (p, q) = untuple pq
        in equalLocHeapOp w
             [< LocHeapCoalg .map idLeft k0
             ,  p
             ,  q
             ,  LocHeapCoalg .map idLeft k1
             ]
      coalg : BoxCoalg ((LocHeap t) ^ EqualTestType .Arity)
      coalg = ArityExponential {ws = EqualTestType .Arity} LocHeapCoalg
  in (cast coalg).curry op'

LocHeapAlgebra : {t : Type} -> LSAlgebra (LocHeap t)
LocHeapAlgebra = [
  readLocHeapOp',
  writeLocHeapOp' False,
  writeLocHeapOp' True,
  equalLocHeapOp',
  newLocHeapOp' False,
  newLocHeapOp' True
]

pureLocHeap : LocHeap Unit w
pureLocHeap w rho = pureHeap ()

initialLocHeap : LocHeap Unit [< P, P]
initialLocHeap w rho =
  let l1 = rho _ Here
      l2 = rho _ (There Here)
  in case w of
    [<] => \_ => ((), [<])         -- No physical locations
    [< P] => \x => ((), x)         -- One physical location
    (w :< P) :< P => \x => ((), x) 

-- l1 := !l2
readWrite : {f : Family} -> {auto fPsh : BoxCoalg f} -> (w : World) ->
  Env [< P] w ->     -- Location 1
  Env [< P] w ->     -- Location 2
  LSFreeMonad f w -> -- Continuation
  LSFreeMonad f w
readWrite w l1 l2 k =
  let k' = \b => write b w [< l1, k]
  in read w [< k' True, l2, k' False]

-- swap value of two locations with temp location
-- temp = new 0
-- temp := !l1
-- l1 := !l2
-- l2 := !temp
swap : {f : Family} -> {auto fPsh : BoxCoalg f} -> (w : World) ->
  Env [< P] w ->                -- Location 1
  Env [< P] w ->                -- Location 2
  LSFreeMonad f w -> -- Continuation
  LSFreeMonad f w
swap w l1 l2 k =
  let coalg = BoxCoalgFree fPsh in
  new False _ (
    let temp : [<P] ~> [< P] ++ w
        temp = inl
        l1' = inr . l1
        l2' = inr . l2
    in
    readWrite _ temp l1' $
    readWrite _ l1' l2' $
    readWrite _ l2' temp $
    coalg.map inr k
  )

Ex1 : {f : Family} -> {auto fPsh : BoxCoalg f} ->
  f [< P, P] -> LSFreeMonad f [< P, P]
Ex1 val =
  let l1 = inl {w2 = [< P]}
      l2 = inr
  in swap _ l1 l2 (pure _ val)

RunEx1 : (w' : World) -> ([< P, P] ~> w') -> StateIn w' -> StateIn w'
RunEx1 w' rho ss =
  let interpret = (LocHeapAlgebra .fold) LocHeapCoalg idFam
      res = interpret [< P, P] (Ex1 {f = LocHeap Unit} initialLocHeap)
  in snd (runLocHeap w' rho res ss)

Ex2 : {f : Family} -> {auto fPsh : BoxCoalg f} ->
  f [< P, P, P] -> LSFreeMonad f [< P, P, P]
Ex2 val =
  -- [< l1, l2, l3]
  let l1 : [< P] ~> [< P] ++ [<P, P]
      l1 = inl {w2 = [< P, P]}
      l2 : [< P] ~> ([< P] ++ [< P]) ++ [< P]
      l2 = inr {w1 = [< P], w2 = [< P, P]} . inl {w1 = [< P], w2 = [< P]}
      l3 : [< P] ~> [< P, P] ++ [< P]
      l3 = inr
  in
  readWrite _ l1 l2 $ -- l1 := !l2
  readWrite _ l2 l3 $ -- l2 := !l3
  pure _ val
  -- [< l3, l3, l3]

RunEx2 : (w' : World) -> ([< P, P, P] ~> w') -> StateIn w' -> StateIn w'
RunEx2 w' rho ss =
  let interpret = (LocHeapAlgebra .fold) LocHeapCoalg idFam
      res = interpret [< P, P, P] (Ex2 {f = LocHeap Unit} pureLocHeap)
  in snd (runLocHeap w' rho res ss)