module Paella

import public Data.DPair

import public Data.SnocList
import public Data.SnocList.Extra
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

namespace Data.Snoclist.Extra
  public export
  (!!) : (sx : SnocList a) -> (Fin (length sx)) -> a
  (!!) = index'

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
(.:.) : {f, g, h : Family} -> (g -|> h) -> (f -|> g) -> (f -|> h)
(beta .:. alpha) w = beta w . alpha w

--------------------------------------------
-- The category of presheaves over worlds --
--------------------------------------------

-- Our presheaves do not have proof of functorial action attached to them since
-- we perform no proofs elsewhere

||| A family is a presheaf when equipped with a functorial action
public export
PresheafOver : Family -> Type
PresheafOver f = {w1, w2 : World} -> (rho : w1 ~> w2) -> (f w1 -> f w2)

infixr 1 =|>

namespace Coalgebra
  ||| A presheaf structure given in end form
  ||| The right-adjoint Fiore-transform comonad (Box)
  public export
  Box : Family -> Family
  Box f a = (b : World) -> (a ~> b) -> f b

  ||| Fiore transform: a `BoxCoalg` (with laws) is equivalent to a presheaf
  ||| (with laws)
  public export
  record BoxCoalg (f : Family) where
    constructor MkBoxCoalg
    next : f -|> Box f

  ||| A `BoxCoalg` gives a functorial action
  public export
  (.map) : {f : Family} -> BoxCoalg f -> PresheafOver f
  coalg.map {w1,w2} rho v = coalg.next w1 v w2 rho

  ||| A coalgebra map, if we had laws this would be the same as a natural
  ||| transformation
  public export
  (=|>) : {f, g : Family} -> (fAlg : BoxCoalg f) -> (gAlg : BoxCoalg g) -> Type
  (=|>) {f, g} _ _ = f -|> g

||| A functorial action for a family induces a box coalgebra
public export
{f : _} -> Cast (PresheafOver f) (BoxCoalg f) where
  cast psh = MkBoxCoalg $ \w, x, w', rho => psh rho x

||| A box coalgebra for a family induces a functorial action
public export
{f : _} -> Cast (BoxCoalg f) (PresheafOver f) where
  cast coalg = coalg.map

-- Basic presheaves

||| The constant family is a presheaf
public export
BoxCoalgConst : {t : Type} -> BoxCoalg (const t)
BoxCoalgConst = MkBoxCoalg $ \_, x, _, _ => x

||| The family of variables of type `a` is a presheaf
public export
BoxCoalgVar : {a : A} -> BoxCoalg (Var a)
BoxCoalgVar = MkBoxCoalg $ \w, pos, w', rho => rho a pos

-- Representable functors

||| The representable functor at `w`, so a map `Env w -|> f` is morally an
||| element of `f w` and thus `f` in environment `w`
public export
Env : World -> Family
Env w = (w ~>)

BoxCoalgEnv : {w1 : World} -> BoxCoalg (Env w1)
BoxCoalgEnv = MkBoxCoalg $ \w, rho, w', rho' => rho' . rho

-- Product structure

||| The product of families is given pointwise
public export
FamProd : SnocList Family -> Family
FamProd sf w = ForAll sf $ \f => f w

||| When each family in a product of families is a presheaf, then so is the
||| product
public export
BoxCoalgProd : {sf : SnocList Family} ->
  ForAll sf BoxCoalg -> BoxCoalg $ FamProd sf
BoxCoalgProd scoalg = MkBoxCoalg $ \w, sx, w', rho =>
  zipPropertyWithRelevant (\f, coalg, x => coalg.map rho x) scoalg sx

||| Given a collection of maps out of a family `f`, we can tuple them together
public export
tuple : {f : Family} -> {sg : SnocList Family} ->
  ForAll sg (\g => f -|> g) -> (f -|> FamProd sg)
tuple sh w x = mapProperty (\h => h w x) sh

||| Projection out of a product of families
projection : {sf : SnocList Family} ->
  (i : Fin $ length sf) -> FamProd sf -|> (sf !! i)
projection i w sx = indexAll (indexIsElem sf i) sx

||| Product of families is symmetric
public export
swap : FamProd [< f, g] -|> FamProd [< g, f]
swap w [< x, y] = [< y, x]

-- Coproduct structure

||| When each family in a sum of families is a presheaf, then so is the sum
public export
FamSum : SnocList Family -> Family
FamSum sf w = ForAny sf $ \f => f w

||| Presheaf structure of sum presheaf
public export
BoxCoalgSum : {sf : SnocList Family} ->
  ForAll sf BoxCoalg -> BoxCoalg $ FamSum sf
BoxCoalgSum salg =  MkBoxCoalg $ \w, sx, w', rho =>
  applyAtAny (\f, coalg => coalg.map rho) salg sx

-- Exponentiating by representables, transformed

||| Fiore-transform of presheaf exponentiation of `f` by Yoneda of `w1`
public export
(.shift) : World -> Family -> Family
w1.shift f w2 = f (w1 ++ w2)

||| Fiore-transform of presheaf exponentiation of `f` by Yoneda of `w1`, swapped
public export
(.shiftLeft) : World -> Family -> Family
w1.shiftLeft f w2 = f (w2 ++ w1)

||| Exponentiating a presheaf by a representable gives a presheaf
public export
(.shiftCoalg) : {f : Family} ->
  (w1 : World) -> BoxCoalg f -> BoxCoalg (w1.shift f)
w1.shiftCoalg coalg = MkBoxCoalg $ \w, x, w', rho =>
  coalg.map (bimap {w1 = w1} idRen rho) x

||| Exponentiating a presheaf by a representable gives a presheaf, swapped
public export
(.shiftLeftCoalg) : {f : Family} ->
  (w1 : World) -> BoxCoalg f -> BoxCoalg (w1.shiftLeft f)
w1.shiftLeftCoalg coalg = MkBoxCoalg $ \w, x, w', rho =>
  coalg.map (bimap {w2 = w1} rho idRen) x

||| `w1.shift f` is an exponential of `f` by `Env w1`, thus has an evaluation
public export
(.evalRep) : {w1 : World} -> {f : Family} -> (coalg : BoxCoalg f) ->
  FamProd [< w1.shift f, Env w1] -|> f
coalg.evalRep w [< u, rho] = coalg.map (cotuple rho idRen) u

||| `w1.shift g` is an exponential of `g` by `Env w1`, thus has an currying
public export
(.curryRep) : {w1 : World} -> {f : Family} -> (coalg : BoxCoalg f) ->
  (FamProd [< f, Env w1] -|> g) -> (f -|> w1.shift g)
coalg.curryRep alpha w u = alpha (w1 ++ w) [< coalg.map inr u, inl]

public export
(.curryRep') : {w1 : World} -> {f, g : Family} -> (coalg : BoxCoalg f) ->
  (FamProd [< Env w1, f] -|> g) -> (f -|> w1.shift g)
coalg.curryRep' alpha = coalg.curryRep (alpha .:. swap)

||| `w1.shift g` is an exponential of `g` by `Env w1`, thus has an uncurrying
public export
(.uncurryRep) : {w1 : World} -> {g : Family} -> (coalg : BoxCoalg g) ->
  (f -|> w1.shift g) -> (FamProd [< f, Env w1] -|> g)
coalg.uncurryRep beta w [< u, rho] = coalg.map (cotuple rho idRen) (beta w u)

-- Exponentiating by a sum of representables, as a product

infixl 7 ^

||| The exponentiation of `f` by the sum of representables of `ws`
public export
(^) : Family -> SnocList World -> Family
f ^ ws = FamProd (map (\w => w.shift f) ws)

||| Exponentiating a presheaf by a sum of representables gives a presheaf
public export
BoxCoalgExpSum : {f : Family} -> {ws : SnocList World} ->
  BoxCoalg f -> BoxCoalg (f ^ ws)
BoxCoalgExpSum coalg =
  BoxCoalgProd $ propertyToMap $ tabulate _ $ \w => w.shiftCoalg coalg

||| Exponentiating by a sum of representables has an evaluation
public export
(.evalSum) : {ws : SnocList World} -> {f : Family} -> (coalg : BoxCoalg f) ->
  FamProd [< f ^ ws, FamSum (map Env ws)] -|> f
coalg.evalSum w [< u, rho] =
  forget $ applyAtAny' (\_, x, rho' => coalg.map (cotuple rho' idRen) x) u rho

||| Exponentiating by a sum of representables has a currying
public export
(.currySum) : {ws : SnocList World} -> {f : Family} -> (coalg : BoxCoalg f) ->
  (FamProd [< f, FamSum (map Env ws)] -|> g) -> (f -|> g ^ ws)
coalg.currySum {ws = [<]} alpha w u = [<]
coalg.currySum {ws = ws' :< w'} alpha w u =
  propertyToMap $ tabulateElem (ws' :< w') (\w1, pos =>
    alpha (w1 ++ w)
      [< coalg.map inr u
      ,  propertyToMap {sx = ws' :< w'} {f = Env} (inject pos inl)
      ]
  )

||| Exponentiating by a sum of representables has an uncurrying
public export
(.uncurrySum) : {ws : SnocList World} -> {g : Family} -> (coalg : BoxCoalg g) ->
  (f -|> g ^ ws) -> (FamProd [< f, FamSum (map Env ws)] -|> g)
coalg.uncurrySum beta w [< u, rho] = forget $
  applyAtAny' (\_, x, rho' => coalg.map (cotuple rho' idRen) x) (beta w u) rho

||| Post-composition for exponentiating by a sum of representables
public export
expSumMap : {ws : SnocList World} -> {f, g : Family} ->
  (f -|> g) -> (f ^ ws -|> g ^ ws)
expSumMap alpha w sx = mapPropertyWithRelevant' (\x, y => alpha (x ++ w) y) sx

-- General exponential of presheaves

infixr 2 -%

||| Exponential of presheaves
public export
(-%) : (f, g : Family) -> Family
(f -% g) w = (FamProd [< Env w, f]) -|> g

||| Evaluation for exponential
public export
eval : FamProd [< f -% g, f] -|> g
eval w [< alpha, x] = alpha w [< idRen, x]

||| Currying for exponential
public export
(.curry) : {h : Family} -> (coalg : BoxCoalg h) ->
  (FamProd [< h, f] -|> g) -> (h -|> (f -% g))
coalg.curry beta w env w' [< rho, x] = beta w' [< coalg.map rho env, x]

||| Uncurrying for exponential
public export
uncurry : {h : Family} -> (h -|> (f -% g)) -> (FamProd [< h, f] -|> g)
uncurry h w [< env, x] = h w env w [< idRen, x]

||| The exponential of two presheaves is a presheaf
public export
BoxCoalgExp : BoxCoalg (f -% g)
BoxCoalgExp = MkBoxCoalg $ \w, alpha, w', rho, w'', [< rho', x] =>
  alpha w'' [< rho' . rho, x]

||| Post-composition for exponentiating
public export
expMap : {f, g, h : Family} ->
  (f -|> g) -> (h -% f -|> h -% g)
expMap {f, g, h} alpha = BoxCoalgExp .curry (alpha .:. eval)

||| Swap the arguments of a curried function
-- instead of mess around with point-free style, switch to pointed style
public export
(.swapExps) : {f, g, h : Family} -> (coalg : BoxCoalg g) ->
  f -% (g -% h) -|> g -% (f -% h)
coalg.swapExps =
  (BoxCoalgExp).curry $ (BoxCoalgProd [< BoxCoalgExp , coalg]).curry $
    \w, [<[< a, y], x] => eval w [< eval w [< a, x], y]

||| Turn a real exponential by a representable into the special case
public export
shiftIntoRepr : {w1 : World} -> {g : Family} ->
  (Env w1 -% g) -|> (w1.shift g)
shiftIntoRepr = BoxCoalgExp .curryRep eval

||| Turn the special case of exponentiating by a representable into a real
||| exponential
public export
(.shiftFromRepr) : {w1 : World} -> {g : Family} -> (coalg : BoxCoalg g) ->
   (w1.shift g) -|> (Env w1 -% g)
coalg.shiftFromRepr = (w1.shiftCoalg coalg).curry coalg.evalRep

----------------------------------------------------
-- Free monad for algebraic effects in presheavss --
----------------------------------------------------

public export
record OpSig where
  constructor MkOpSig
  Args  : Family
  Arity : Family

public export
Signature : Type
Signature = List OpSig

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
  Args  : BoxCoalg op.Args
  Arity : BoxCoalg op.Arity

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
        [< (indexAll pos sigFunc).Args.map rho arg
        , BoxCoalgExp .map rho cont]

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
  (\x => BoxCoalgExp .curry)

public export
liftOp : {gamma, arity, args, f : Family} ->
  (BoxCoalg args) => (BoxCoalg gamma) =>
  (op : arity -% f -|> args -% f) ->
  (arity -% (gamma -% f) -|> args -% (gamma -% f))
liftOp @{argsPsh} @{gammaPsh} op =
  argsPsh.swapExps .:. (expMap op) .:. gammaPsh.swapExps

public export
liftAlg : {sig : Signature} -> {gamma, f : Family} ->
  (sigFuncs : FunctorialSignature sig) =>
  (gammaPsh : BoxCoalg gamma) =>
  sig.AlgebraOver f ->
  sig.AlgebraOver (gamma -% f)
liftAlg @{sigFuncs} alg = zipPropertyWithRelevant (\optor,sigFunc, op =>
    liftOp @{sigFunc.Args} @{gammaPsh} op)
  sigFuncs alg

public export
curryOp : (sig : Signature) ->
  (f : Family) -> (BoxCoalg f) ->
  (op : OpSig) -> op `Elem` sig ->
  op.Arity -% (sig.Free f) -|> (op.Args) -% (sig.Free f)
curryOp sig f coalg op pos =
  BoxCoalgExp .curry (Op pos .:. swap)

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
      folded = g_op (expMap {h = op.Arity} fold w k)
  in eval w [< folded, arg]

public export
(.extend) :  {sig : Signature} -> {f,g : Family} -> BoxCoalg g ->
  (f -|> sig.Free g) -> (sig.Free f -|> sig.Free g)
gPsh.extend alpha = (TermAlgebra g gPsh).fold alpha

public export
(.extendStrength) :  {sig : Signature} ->
  (sigFuncs : FunctorialSignature sig) =>
  {gamma, f,g : Family} ->
  {fCoalg : BoxCoalg f} ->
  {gammaPsh : BoxCoalg gamma} ->
  BoxCoalg g ->
  (FamProd [< gamma, f] -|> sig.Free g) ->
  (FamProd [< gamma, sig.Free f] -|> sig.Free g)
gPsh.extendStrength alpha  =
  (uncurry $ (liftAlg @{sigFuncs} @{gammaPsh} (TermAlgebra g gPsh)).fold (fCoalg.curry $ alpha .:. swap)) .:. swap

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
  ((coalg.extendStrength {sigFuncs} {fCoalg = fPsh}
                   {gammaPsh =
                   (BoxCoalgProd $ mapPropertyWithRelevant (\_,psh => psh) gammaPsh)})
                (\w,[< env, x] => k w (env :< x)))
      .:. tuple [<\_ => id,  xs]

public export
(.join) : {sig : Signature} -> {f : Family} -> BoxCoalg f ->
  sig.Free (sig.Free f) -|> sig.Free f
fPsh.join = fPsh.extend idFam