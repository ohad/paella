module Paella

import public Data.DPair

import public Data.SnocList
import public Data.SnocList.Elem
import public Data.SnocList.Quantifiers

import public Data.List
import public Data.List.Elem
import public Data.List.Quantifiers

import public Data.Fin

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
  zipPropertyWithRelevant : {xs : List _} ->
    ((x : _) -> p x -> q x -> r x) -> All p xs -> All q xs -> All r xs
  zipPropertyWithRelevant f [] vs = []
  zipPropertyWithRelevant f (u :: us) (v :: vs) =
    f _ u v :: zipPropertyWithRelevant f us vs

  public export
  mapPropertyWithRelevant : {xs : List _} ->
    ((x : _) -> p x -> q x) -> All p xs -> All q xs
  mapPropertyWithRelevant f [] = []
  mapPropertyWithRelevant f (y :: ys) =
    f _ y :: mapPropertyWithRelevant f ys

infix 3 !! , ::= , ?!

-- This should be in stdlib somewhere, probably not as infix notation

namespace Data.List.Fin
  public export
  (!!) : (xs : List a) -> (Fin (length xs)) -> a
  [] !! pos impossible
  (x :: xs) !!  FZ      = x
  (x :: xs) !! (FS pos) = xs !! pos

  public export
  (?!) : (xs : List a) -> (i : Fin (length xs)) ->
         (xs !! i) `Elem` xs
  [] ?! i impossible
  (x :: xs) ?!  FZ = Here
  (x :: xs) ?! (FS pos) = There (xs ?! pos)

namespace Data.SnocList.Fin
  public export
  (!!) : (xs : SnocList a) -> (Fin (length xs)) -> a
  [<] !! pos impossible
  (xs :< x) !!  FZ      = x
  (xs :< x) !! (FS pos) = xs !! pos

  public export
  (?!) : (xs : SnocList a) -> (i : Fin (length xs)) ->
         (xs !! i) `Elem` xs
  [<] ?! i impossible
  (xs :< x) ?!  FZ = Here
  (xs :< x) ?! (FS pos) = There (xs ?! pos)


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
public export
data A = ConsCell

public export
||| A 0-th order context, operation's arities will be a
||| finite list of worlds.
World : Type
World = SnocList A

||| A `x : Var a w` is a first-order variable of paramter type `a` in `w`
public export
data Var : A -> World -> Type where
  Here : Var a (w :< a)
  There : Var a w -> Var a (w :< b)

infixr 1 ~>

public export
||| A renaming from src to tgt, sending each variable in src to a
||| variable in tgt
(~>) : (src, tgt : World) -> Type
w1 ~> w2 = (a : A) -> Var a w1 -> Var a w2

public export
-- (World, (~>)) is a category
idRen : w ~> w
idRen a x = x

public export
(.) : w2 ~> w3 -> w1 ~> w2 -> w1 ~> w3
(.) f g a x = f a (g a x)

public export
Family : Type
Family = World -> Type

infixr 1 -|>, =|>, .:.

public export
-- Family transformation
(-|>) : (f, g : Family) -> Type
f -|> g = (w : World) -> f w -> g w

public export
-- Closed version
(.elem) : (f : Family) -> Type
f.elem = (w : World) -> f w


public export
idFam : {f : Family} -> f -|> f
idFam w x = x

public export
(.:.) : {f,g,h : Family} -> g -|> h -> f -|> g -> f -|> h
(beta .:. alpha) w = beta w . alpha w

public export
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

public export
{f : _} -> Cast (DAlg f) (BoxCoalg f) where
  cast alg = MkBoxCoalg $ \w, x, w', rho => alg.map rho x

public export
{f : _} -> Cast (BoxCoalg f) (DAlg f) where
  cast coalg = MkDAlg $ \w, closure => coalg.map closure.weaken closure.val

public export
{f : _} -> Cast (PresheafOver f) (BoxCoalg f) where
  cast psh = MkBoxCoalg $ \w, x, w', rho => psh rho x

public export
{f : _} -> Cast (PresheafOver f) (DAlg f) where
  cast psh = MkDAlg $ \w, closure =>
    psh closure.weaken closure.val

public export
||| Fiore-transform of presheaf exponentiation: f^(Yoneda w1).
(.shift) : World -> Family -> Family
w1.shift f w2 = f (w1 ++ w2)

public export
(.shiftLeft) : World -> Family -> Family
w1.shiftLeft f w2 = f (w2 ++ w1)

public export
split : {w2 : World} -> Var a (w1 ++ w2) -> Either (Var a w1) (Var a w2)
split {w2 = [<]     } x = Left x
split {w2 = pos :< a} Here = Right Here
split {w2 = pos :< b} (There x) = bimap id (There) (split x)

public export
inl : {w2 : World} -> w1 ~> w1 ++ w2
inl {w2 = [<]} a x = x
inl {w2 = w2 :< b} a x = There (inl a x)

public export
inr : w2 ~> w1 ++ w2
inr {w2 = .(w2 :< a)} a Here = Here
inr {w2 = .(w2 :< b)} a (There x) = There (inr a x)

public export
cotuple : {w2 : World} -> (w1 ~> w) -> (w2 ~> w) -> w1 ++ w2 ~> w
cotuple {w2 = [<]    } f g   a  x        = f a x
cotuple {w2 = w2 :< b} f g .(b) Here     = g b Here
cotuple {w2 = w2 :< b} f g   a (There x) = cotuple f (\c, y => g c (There y)) a x

public export
swapRen : {w1, w2 : World} -> (w1 ++ w2) ~> (w2 ++ w1)
swapRen = cotuple inr inl

public export
||| Monoidal action on maps
bimap : {w1, w2, w1', w2' : World} -> (w1 ~> w1') -> (w2 ~> w2') -> (w1 ++ w2) ~> (w1' ++ w2')
bimap f g a x = case split x of
  Left  y => inl a (f a y)
  Right y => inr a (g a y)

public export
-- (f.shift) is actually a presheaf
(.shiftAlg) : (w1 : World) -> {f : Family} -> DAlg f -> DAlg (w1.shift f)
w1.shiftAlg {f} alg = MkDAlg $ \w, (Close ctx rho v) =>
  alg.map (Paella.bimap idRen rho) v

public export
(.shiftCoalg) : (w1 : World) -> {f : Family} -> BoxCoalg f -> BoxCoalg (w1.shift f)
w1.shiftCoalg {f} boxCoalg = cast (w1.shiftAlg $ cast {to = DAlg f} boxCoalg)

public export
||| The product family is given pointwise
FamProd : SnocList Family -> Family
FamProd sf w = ForAll sf $ \f => f w

public export
||| Presheaf structure of product presheaf
BoxCoalgProd : {sf : SnocList Family} -> ForAll sf (\f => BoxCoalg f) ->
  BoxCoalg $ FamProd sf
BoxCoalgProd sbox = MkBoxCoalg $ \w, sx, w', rho =>
  zipPropertyWithRelevant (\f,box,x => box.map rho x)
    sbox
    sx

public export
tuple : {f : Family} -> {sg : SnocList Family} ->
  ForAll sg (\g => f -|> g) ->
  f -|> FamProd sg
tuple hs w x = mapProperty (\h => h w x) hs

{- TODO: For completeness
projection : {sf : SnocList Family} -> (i : Fin $ length sf) ->
  FamProd sf -|> (sf !! i)
-}

public export
Env : World -> Family
Env w = (w ~>)

public export
swap : FamProd [< f , g] -|> FamProd [< g, f]
swap w [< x , y] = [< y , x]

public export
-- (f.shift) is actually an exponential
(.eval) : {w1 : World} -> {f : Family} -> (fPsh : DAlg f) ->
       FamProd [< w1.shift f, Env w1] -|> f
fPsh.eval w [< u, rho] = fPsh.map (cotuple rho idRen) u

public export
(.curry) : {w1 : World} -> {f : Family} -> (fPsh : DAlg f) ->
  (FamProd [< f, Env w1] -|> g) -> f -|> w1.shift g
fPsh.curry alpha w u = alpha (w1 ++ w) [< fPsh.map inr u, inl]

public export
(.curry') : {w1 : World} -> {f : Family} -> (fPsh : DAlg f) ->
  (FamProd [< Env w1, f] -|> g) -> f -|> w1.shift g
fPsh.curry' alpha w u = alpha (w1 ++ w) [< inl, fPsh.map inr u]

public export
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

public export
uncur : {gamma : Family} ->
  gamma -|> (f -% g) ->
  FamProd[< gamma, f] -|> g
uncur h w [< env, x] = h w env w [< idRen, x]

-- Can derive from previous but can cut out hassle
public export
abst :
  (f -|> g) ->
  (f -% g).elem
abst f w w' [< rho , x] = f w' x

public export
ExpCoalg : BoxCoalg (f -% g)
ExpCoalg = MkBoxCoalg $ \w, alpha, w', rho, w'', [< rho' , x] =>
  alpha w'' [< rho' . rho, x]

public export
(.shiftIntoRepr) : {w0 : World} -> {g : Family} ->
  (PresheafOver g) ->
  ((Env w0) -% g) -|> (w0.shift g)
psh.shiftIntoRepr =
  (cast {from = BoxCoalg (Env w0 -% g)} $ ExpCoalg).curry
    {g, f = (Env w0) -% g} $ eval {f = Env w0, g = g}

public export
(.shiftFromRepr) : {w0 : World} -> {g : Family} ->
  (PresheafOver g) ->
   (w0.shift g) -|> ((Env w0) -% g)
psh.shiftFromRepr =
  let coalg : BoxCoalg g = cast psh
      algeb = (cast {to = DAlg g} psh).eval
  in (w0.shiftCoalg coalg).map.abst algeb

public export
-- Did we not define this already?
varCoalg : {a : A} -> BoxCoalg (Var a)
varCoalg = MkBoxCoalg $ \w, pos, w', rho => rho a pos

public export
record OpSig where
  constructor MkOpSig
  Args  : Family
  Arity : Family

public export
Signature : Type
Signature = List OpSig

infixl 7 ^

public export
||| The exponentiation of f by the sum of representables coprod_{w in ws} y(w)
(^) : Family -> SnocList World -> Family
f ^ ws = FamProd (map (\w => w.shift f) ws)

public export
ArityExponential : {f : Family} -> (BoxCoalg f) ->
  {ws : SnocList World} -> BoxCoalg (f ^ ws)
ArityExponential {f, ws} boxCoalg
  = BoxCoalgProd $ rippleAll $ tabulate _
                 $ \w => w.shiftCoalg boxCoalg

public export
||| The sum family is given pointwise
FamSum : SnocList Family -> Family
FamSum sf w = ForAny sf $ \f => f w

public export
||| Presheaf structure of sum presheaf
BoxCoalgSum : {sf : SnocList Family} -> ForAll sf (\f => BoxCoalg f) ->
  BoxCoalg $ FamSum sf
BoxCoalgSum salg =  MkBoxCoalg $ \w, sx, w', rho => applyAny (\f, coalg => coalg.map rho) salg sx

public export
-- (f ^ ws) is actually an exponential
(.evalSum) : {ws : SnocList World} -> {f : Family} -> (fPsh : DAlg f) ->
       FamProd [< f ^ ws, FamSum (map Env ws)] -|> f
fPsh.evalSum w [< u, rho] =
  forgetAny $ applyMapAllAny
                (\w1,x,rho => fPsh.map (cotuple rho idRen) x)
                u
                rho

public export
(.currySum) : {ws : SnocList World} -> {f : Family} -> (fPsh : DAlg f) ->
  (FamProd [< f, FamSum (map Env ws)] -|> g) -> f -|> g ^ ws
fPsh.currySum {ws = [<]} alpha w u = [<]
fPsh.currySum {ws = ws' :< w'} alpha w u =
  rippleAll (tabulateElem (ws' :< w')
  (\w1, pos => alpha (w1 ++ w) [< fPsh.map inr u, rippleAny {xs = ws' :< w'} {f = Env} (injectAny pos inl)]))

public export
(.uncurrySum) : {ws : SnocList World} -> {g : Family} -> (gPsh : DAlg g) ->
  (f -|> g ^ ws) -> (FamProd [< f, FamSum (map Env ws)] -|> g)
gPsh.uncurrySum beta w [< u, rho] =
  forgetAny $ applyMapAllAny (\w1, x, rho' => gPsh.map (cotuple rho' idRen) x) (beta w u) rho

public export
expMapSumRep : {ws : SnocList World} ->
  {f,g : Family} ->
  (f -|> g) -> (f ^ ws) -|> (g ^ ws)
expMapSumRep alpha w sx = mapAll (\x, y => alpha (x ++ w) y) sx

public export
expMap :
  {f,g,e : Family} ->
  (f -|> g) -> (e -% f) -|> (e -% g)
expMap {f,g,e} alpha = ExpCoalg .map.abst (alpha .:. eval)

public export
data (.Free) : Signature -> Family -> Family where
  Return : x -|> sig.Free x
  Op : {op : OpSig} ->
    {x : Family} ->
    op `Elem` sig ->
    -- Argument
    FamProd [< op.Args , op.Arity -% sig.Free x]
    -|> sig.Free x

public export
record FunctorialOpSig (op : OpSig) where
  constructor MkFunOpSig
  Args  : PresheafOver op.Args
  Arity : PresheafOver op.Arity

public export
FunctorialSignature : Signature -> Type
FunctorialSignature sig = ForAll sig $ FunctorialOpSig

public export
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

public export
(.AlgebraOver) : Signature -> Family -> Type
sig.AlgebraOver f = ForAll sig $ \op =>
  (op.Arity -% f) -|> (op.Args -% f)

public export
MkAlgebraOver : {sig : Signature} -> {f : Family} ->
  (ForAll sig $ \op =>
    (FamProd [< op.Arity -% f , op.Args] -|> f))
  -> sig.AlgebraOver f
MkAlgebraOver = mapPropertyWithRelevant
  (\x => ExpCoalg .map.abst)


-- Powers

public export
swapExps : {a,b,f : Family} ->
  (PresheafOver b) =>
  a -% (b -% f) -|> b -% (a -% f)
swapExps @{bPsh} =
  (ExpCoalg).map.abst
    ((BoxCoalgProd [< ExpCoalg , cast {from = PresheafOver b} bPsh]).map.abst $
  -- instead of mess around with point-free style, switch to pointed style
  \w, [<[< h, x], y] => eval w [< eval w [< h, y], x]
  )

public export
liftOp : {gamma, arity, args, f : Family} ->
  (PresheafOver arity) => (PresheafOver args) => (PresheafOver gamma) =>
  (op : arity -% f -|> args -% f) ->
  (arity -% (gamma -% f) -|> args -% (gamma -% f))
liftOp @{arityPsh} @{argsPsh} @{gammaPsh} op =
  swapExps @{argsPsh} .:. (expMap op) .:. swapExps @{gammaPsh}

public export
liftAlg : {sig : Signature} -> {gamma, f : Family} ->
  (sigFuncs : FunctorialSignature sig) =>
  (gammaPsh : PresheafOver gamma) =>
  sig.AlgebraOver f ->
  sig.AlgebraOver (gamma -% f)
liftAlg @{sigFuncs} alg = zipPropertyWithRelevant (\optor,sigFunc, op =>
    liftOp @{sigFunc.Arity} @{sigFunc.Args} @{gammaPsh} op)
  sigFuncs alg

public export
curryOp : (sig : Signature) ->
  (f : Family) -> (BoxCoalg f) ->
  (op : OpSig) -> op `Elem` sig ->
  op.Arity -% (sig.Free f) -|> (op.Args) -% (sig.Free f)
curryOp sig f coalg op pos =
  (ExpCoalg .map).abst (Op pos .:. swap)

public export
TermAlgebra : {sig : Signature} ->
  (f : Family) -> (BoxCoalg f) -> sig.AlgebraOver (sig.Free f)
TermAlgebra {sig} f coalg = tabulateElem sig $
  curryOp sig f coalg

public export
pure : {sig : Signature} -> {f : Family} -> f -|> sig.Free f
pure = Return

public export
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

public export
(.extend) :  {sig : Signature} -> {f,g : Family} -> BoxCoalg g ->
  (f -|> sig.Free g) -> (sig.Free f -|> sig.Free g)
gPsh.extend alpha = (TermAlgebra g gPsh).fold alpha

public export
(.extendStrength) :  {sig : Signature} ->
  (sigFuncs : FunctorialSignature sig) =>
  {gamma, f,g : Family} ->
  {fPsh : PresheafOver f} ->
  {gammaPsh : PresheafOver gamma} ->
  BoxCoalg g ->
  (FamProd [< gamma, f] -|> sig.Free g) ->
  (FamProd [< gamma, sig.Free f] -|> sig.Free g)
gPsh.extendStrength alpha  =
  (uncur $ (liftAlg @{sigFuncs} @{gammaPsh} (TermAlgebra g gPsh)).fold (fPsh.abst $ alpha .:. swap)) .:. swap

infixr 1 >>==

public export
(>>==) : {sig : Signature} ->
  {gammas : SnocList Family} ->
  {f,g : Family} ->
  (sigFuncs : FunctorialSignature sig) =>
  (gammaPsh : ForAll gammas BoxCoalg) =>
  (fPsh : BoxCoalg f) =>
  (coalg : BoxCoalg g)  =>
  (FamProd gammas -|> sig.Free f) ->
  (FamProd (gammas :< f) -|> sig.Free g) ->
  FamProd gammas -|> sig.Free g
(>>==) xs k =
  ((coalg.extendStrength {sigFuncs} {fPsh = fPsh.map}
                   {gammaPsh =
                   (BoxCoalgProd $ mapPropertyWithRelevant (\_,psh => psh) gammaPsh).map})
                (\w,[< env, x] => k w (env :< x)))
      .:. tuple [<\_ => id,  xs]

public export
(.join) : {sig : Signature} -> {f : Family} -> BoxCoalg f ->
  sig.Free (sig.Free f) -|> sig.Free f
fPsh.join = fPsh.extend idFam

public export
-- Postulate: each parameter has a type
-- For now, just cons cells
TypeOf : A -> Family
TypeOf ConsCell =
  (FamProd [< const String, Var ConsCell])

public export
TypeOfFunctoriality : (a : A) -> PresheafOver $ TypeOf a
-- Should propagate structure more nicely
TypeOfFunctoriality ConsCell rho ([< str , loc]) =
  [< str , rho _ loc]

%hint
public export
TypeOfBoxFunctoriality : (a : A) -> BoxCoalg $ TypeOf a
-- Should propagate structure more nicely
TypeOfBoxFunctoriality a = cast {from = PresheafOver _} (TypeOfFunctoriality a)



public export
||| Type of reading an A-cell
readType : A -> OpSig
readType a = MkOpSig
  { Args = Var a
  , Arity = TypeOf a
  }

public export
||| Type of writing an a
||| w_0 : [a, []]
writeType : A -> OpSig
writeType a = MkOpSig
  { Args = FamProd [< Var a, TypeOf a]
  , Arity = const ()
  }


public export
||| Allocate a fresh cell storing an a value
newType : A -> OpSig
newType a = MkOpSig
  { Args = [< a].shift (TypeOf a)
  , Arity = Var a
  }

public export
LSSig : Signature
LSSig = [
  readType ConsCell,
  writeType ConsCell,
  newType ConsCell
]

%hint
public export
LSSigFunc : FunctorialSignature LSSig
LSSigFunc =
  [ -- read
    MkFunOpSig { Arity = TypeOfFunctoriality ConsCell
               , Args = varCoalg.map
               }
  , -- write
    MkFunOpSig { Arity = const $ const ()
               , Args = (BoxCoalgProd [< varCoalg,
                                         cast {from = PresheafOver (TypeOf ConsCell)}
                                         (TypeOfFunctoriality ConsCell)]).map
               }
  , -- new
    MkFunOpSig { Arity = varCoalg.map
               , Args = ([< ConsCell].shiftCoalg {f = (TypeOf ConsCell)} $
                     cast {from = PresheafOver (TypeOf ConsCell)}
                     (TypeOfFunctoriality ConsCell)).map
               }
  ]

-- Probably better to define the generic operations generically
-- and instantiate to these

public export
read : Var ConsCell -|> LSSig .Free (TypeOf ConsCell)
read w loc =
  Op (LSSig ?! 0) w
     [< loc , abst pure w]

public export
write : FamProd [< Var ConsCell , TypeOf ConsCell] -|>
          LSSig .Free (const ())
write w locval =
  Op (LSSig ?! 1) w
     [< locval , abst pure w]


public export
new : FamProd [< [<ConsCell].shiftLeft (TypeOf ConsCell)] -|>
      LSSig .Free (Var ConsCell)
new w [<val] =
  -- move new location to the bottom of the heap
  let val' = (TypeOfFunctoriality ConsCell)
        (swapRen {w1 = w, w2 = [<ConsCell]}) val
  in Op (LSSig ?! 2) w
    [< val' , abst pure w]

public export
Heaplet : (shape : World) -> Family
Heaplet shape = FamProd (map TypeOf shape)

public export
(!!) : Heaplet shape w -> Var a shape ->
  TypeOf a w
(h :< x) !! Here = x
[<]      !! (There pos) impossible
(h :< x) !! (There pos) = h !! pos

public export
record Update (a : A) (shape, w : World) where
  constructor (::=)
  loc : Var a shape
  val : TypeOf a w

public export
(.update) : Heaplet shape w -> Update a shape w -> Heaplet shape w
(h :< old).update (Here ::= new) = (h :< new)
[<].update (There pos ::= v) impossible
(h :< x).update (There pos ::= v) = h.update (pos ::= v) :< x

public export
HeapletCoalg : {shape : World} -> BoxCoalg (Heaplet shape)
HeapletCoalg = MkBoxCoalg $ \w, heaplet,w',rho =>
  mapAll
    (\a => TypeOfFunctoriality a rho)
    heaplet

public export
Heap : Family
Heap w = Heaplet w w

public export
Ex1 : Heap [< ConsCell, ConsCell]
Ex1 = [< [< "first of singleton", There Here]
      ,  [< "loop" , Here]
      ]

public export
extendHeap : {w : World} ->
  FamProd [< Heap , w.shift $ Heaplet w ] -|> w.shift Heap
extendHeap {w} w' [< heap , init] =
  let u = unrippleAll $ (HeapletCoalg {shape = w'}).map
           (inr {w1 = w}) heap
      v = unrippleAll init
     -- Probably terrible performance, but meh
  in rippleAll (v ++ u)

public export
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
     w1                    w1 ---> w3 = Im[w0] + (w1 - Im[w0]) + (w2 - Im[w0])
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
    inr |       | inr
        v       V
      w+w0 ---> w + w2
        w + rho2
-}

public export
PrivateCoal : {f : Family} ->
  (coalg : BoxCoalg f) -> BoxCoalg (Private f)
PrivateCoal coalg = MkBoxCoalg $ \w, hidden, w', rho => Hide
  { ctx = hidden.ctx
  , val = coalg.map (Paella.bimap idRen rho) hidden.val
  }

public export
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

public export
LSHandlerCarrier : (f : Family) -> Family
LSHandlerCarrier f = Heap -% Private f

public export
LSHandlerPsh : (coalg : BoxCoalg f) ->
  BoxCoalg $ LSHandlerCarrier f
LSHandlerPsh coalg = ExpCoalg

public export
val : {f : Family} -> {coalg : BoxCoalg f} ->
  coalg =|> (LSHandlerPsh coalg)
val = coalg.map.abst $ \w, [< v, heap] =>
  Private.pure {f} w v

public export
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

public export
handle :
  LSSig .Free (const $ List String) [<] ->
  Private (const (List String)) [<]
handle comp =
  let coalg = MkBoxCoalg (\w, strs, b, f => strs)
  in (LSalg {coalg}).fold (val {coalg}) [<] comp [<] [< idRen,[<]]
