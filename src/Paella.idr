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

import public Paella.Worlds
import public Paella.Families
import public Paella.Presheaves
import public Paella.Presheaves.Basic
import public Paella.Presheaves.Exponential
import public Paella.Presheaves.Product
import public Paella.Presheaves.Representable
import public Paella.Presheaves.Sum

infix 3 !!, ::=, ?!

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