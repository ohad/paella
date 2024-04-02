module Paella

import public Data.DPair

import public Data.SnocList
import public Data.SnocList.Elem
import public Data.SnocList.Quantifiers
import public Data.SnocList.Quantifiers.Extra

import public Data.List
import public Data.List.Extra
import public Data.List.Elem
import public Data.List.Quantifiers
import public Data.List.Quantifiers.Extra

import public Data.Fin

infix 3 !!, ::=, ?!

namespace Data.List.Extra
  public export
  (?!) : (xs : List a) -> (i : Fin (length xs)) -> (index' xs i) `Elem` xs
  (?!) = indexIsElem

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
World : Type
World = SnocList A

||| A `x : Var a w` is a first-order variable of paramter type `a` in `w`
public export
data Var : A -> World -> Type where
  Here : Var a (w :< a)
  There : Var a w -> Var a (w :< b)

||| A variable in `w1 ++ w2` is either in `w1` or `w2`
public export
split : {w2 : World} -> Var a (w1 ++ w2) -> Either (Var a w1) (Var a w2)
split {w2 = [<]} x = Left x
split {w2 = _ :< _} Here = Right Here
split {w2 = _ :< _} (There x) = bimap id There (split x)

infixr 1 ~>

||| A renaming from `src` to `tgt`, sending each variable in `src` to a
||| variable in `tgt`, i.e. a morphism of worlds
public export
(~>) : (src, tgt : World) -> Type
w1 ~> w2 = (a : A) -> Var a w1 -> Var a w2

||| Identity renaming
public export
idRen : w ~> w
idRen a x = x

||| Composition of renamings
public export
(.) : w2 ~> w3 -> w1 ~> w2 -> w1 ~> w3
(.) f g a x = f a (g a x)

-- `(++)` is a coproduct in the category of worlds

||| Coproduct inclusion on the left
public export
inl : {w2 : World} -> w1 ~> w1 ++ w2
inl {w2 = [<]} a x = x
inl {w2 = w2 :< b} a x = There (inl a x)

||| Coproduct inclusion on the right
public export
inr : w2 ~> w1 ++ w2
inr {w2 = .(w2 :< a)} a Here = Here
inr {w2 = .(w2 :< b)} a (There x) = There (inr a x)

||| Coproduct cotupling
public export
cotuple : {w2 : World} -> (w1 ~> w) -> (w2 ~> w) -> w1 ++ w2 ~> w
cotuple {w2 = [<]} f g a x = f a x
cotuple {w2 = w2 :< b} f g .(b) Here = g b Here
cotuple {w2 = w2 :< b} f g a (There x) = cotuple f (\c, y => g c (There y)) a x

||| Symmetry of coproduct
public export
swapRen : {w1, w2 : World} -> (w1 ++ w2) ~> (w2 ++ w1)
swapRen = cotuple inr inl

||| Bifunctorial action of coproduct
public export
bimap : {w1, w2, w1', w2' : World} ->
  (w1 ~> w1') -> (w2 ~> w2') -> (w1 ++ w2) ~> (w1' ++ w2')
bimap f g a x = case split x of
  Left  y => inl a (f a y)
  Right y => inr a (g a y)

------------------------------------------
-- The category of families over worlds --
------------------------------------------

||| A `Family` is a family of typs over worlds
public export
Family : Type
Family = World -> Type

infixr 1 -|>, =|>, .:.

||| Family transformation, i.e. a morphism of families
public export
(-|>) : (f, g : Family) -> Type
f -|> g = (w : World) -> f w -> g w

||| Given a family `f`, gives `1 -|> f` i.e. generalized elements
public export
(.elem) : (f : Family) -> Type
f.elem = (w : World) -> f w

||| Identity family transformation
public export
idFam : {f : Family} -> f -|> f
idFam w x = x

||| Composition of family transformations
public export
(.:.) : {f,g,h : Family} -> (g -|> h) -> (f -|> g) -> (f -|> h)
(beta .:. alpha) w = beta w . alpha w

public export
PresheafOver : Family -> Type
PresheafOver f = {w1, w2 : World} -> (rho : w1 ~> w2) ->
  f w1 -> f w2

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
{f : _} -> Cast (PresheafOver f) (BoxCoalg f) where
  cast psh = MkBoxCoalg $ \w, x, w', rho => psh rho x

public export
{f : _} -> Cast (BoxCoalg f) (PresheafOver f) where
  cast coalg = coalg.map

public export
||| Fiore-transform of presheaf exponentiation: f^(Yoneda w1).
(.shift) : World -> Family -> Family
w1.shift f w2 = f (w1 ++ w2)

public export
(.shiftLeft) : World -> Family -> Family
w1.shiftLeft f w2 = f (w2 ++ w1)

public export
(.shiftCoalg) : {f : Family} ->
  (w1 : World) -> BoxCoalg f -> BoxCoalg (w1.shift f)
w1.shiftCoalg coalg = MkBoxCoalg $ \w, x, w', rho =>
  coalg.map (bimap {w1 = w1} idRen rho) x

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

-- {- TODO: For completeness
-- projection : {sf : SnocList Family} -> (i : Fin $ length sf) ->
--   FamProd sf -|> (sf !! i)
-- -}

public export
Env : World -> Family
Env w = (w ~>)

public export
swap : FamProd [< f , g] -|> FamProd [< g, f]
swap w [< x , y] = [< y , x]

public export
-- (f.shift) is actually an exponential
(.eval) : {w1 : World} -> {f : Family} -> (fPsh : BoxCoalg f) ->
       FamProd [< w1.shift f, Env w1] -|> f
fPsh.eval w [< u, rho] = fPsh.map (cotuple rho idRen) u

public export
(.curry) : {w1 : World} -> {f : Family} -> (fPsh : BoxCoalg f) ->
  (FamProd [< f, Env w1] -|> g) -> f -|> w1.shift g
fPsh.curry alpha w u = alpha (w1 ++ w) [< fPsh.map inr u, inl]

public export
(.curry') : {w1 : World} -> {f : Family} -> (fPsh : BoxCoalg f) ->
  (FamProd [< Env w1, f] -|> g) -> f -|> w1.shift g
fPsh.curry' alpha w u = alpha (w1 ++ w) [< inl, fPsh.map inr u]

public export
(.uncurry) : {w1 : World} -> {g : Family} -> (gPsh : BoxCoalg g) ->
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
      algeb = coalg.eval
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
  = BoxCoalgProd $ propertyToMap $ tabulate _
                 $ \w => w.shiftCoalg boxCoalg

public export
||| The sum family is given pointwise
FamSum : SnocList Family -> Family
FamSum sf w = ForAny sf $ \f => f w

public export
||| Presheaf structure of sum presheaf
BoxCoalgSum : {sf : SnocList Family} -> ForAll sf (\f => BoxCoalg f) ->
  BoxCoalg $ FamSum sf
BoxCoalgSum salg =  MkBoxCoalg $ \w, sx, w', rho => applyAtAny (\f, coalg => coalg.map rho) salg sx

public export
-- (f ^ ws) is actually an exponential
(.evalSum) : {ws : SnocList World} -> {f : Family} -> (fPsh : BoxCoalg f) ->
       FamProd [< f ^ ws, FamSum (map Env ws)] -|> f
fPsh.evalSum w [< u, rho] =
  forget $ applyAtAny'
    (\w1,x,rho => fPsh.map (cotuple rho idRen) x)
    u
    rho

public export
(.currySum) : {ws : SnocList World} -> {f : Family} -> (fPsh : BoxCoalg f) ->
  (FamProd [< f, FamSum (map Env ws)] -|> g) -> f -|> g ^ ws
fPsh.currySum {ws = [<]} alpha w u = [<]
fPsh.currySum {ws = ws' :< w'} alpha w u =
  propertyToMap (tabulateElem (ws' :< w')
  (\w1, pos => alpha (w1 ++ w) [< fPsh.map inr u, propertyToMap {sx = ws' :< w'} {f = Env} (inject pos inl)]))

public export
(.uncurrySum) : {ws : SnocList World} -> {g : Family} -> (gPsh : BoxCoalg g) ->
  (f -|> g ^ ws) -> (FamProd [< f, FamSum (map Env ws)] -|> g)
gPsh.uncurrySum beta w [< u, rho] =
  forget $ applyAtAny' (\w1, x, rho' => gPsh.map (cotuple rho' idRen) x) (beta w u) rho

public export
expMapSumRep : {ws : SnocList World} ->
  {f,g : Family} ->
  (f -|> g) -> (f ^ ws) -|> (g ^ ws)
expMapSumRep alpha w sx =
  mapPropertyWithRelevant' (\x, y => alpha (x ++ w) y) sx

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