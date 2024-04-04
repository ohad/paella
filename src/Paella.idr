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

----------------------------------------------------
-- Free monad for algebraic effects in presheaves --
----------------------------------------------------

||| Signature for a single operation, which takes an argument and has a
||| branching arity
public export
record OpSig where
  constructor MkOpSig
  Args  : Family
  Arity : Family

||| A signature is a list of operation signatures
public export
Signature : Type
Signature = List OpSig

||| The free monad on families of algebraic operations
public export
data (.Free) : Signature -> Family -> Family where
  ||| Embeds the family into the monad
  Return : f -|> sig.Free f
  ||| Embeds an operation into the monad
  Op : {op : OpSig} -> {f : Family} ->
    op `Elem` sig ->
    FamProd [< op.Args , op.Arity -% sig.Free f]
    -|> sig.Free f

||| Evidence that the arguments and arity of an operation are presheaves
public export
record BoxCoalgOpSig (op : OpSig) where
  constructor MkFunOpSig
  Args  : BoxCoalg op.Args
  Arity : BoxCoalg op.Arity

||| Evidence that the arguments and arities of all operation in a signature
||| are presheaves
public export
BoxCoalgSignature : Signature -> Type
BoxCoalgSignature sig = ForAll sig $ BoxCoalgOpSig

||| When the signature consists of presheaves and the family is a presheaf, 
||| then the free monad is also a presheaf
export
BoxCoalgFree : {sig : Signature} -> {f : Family} ->
  BoxCoalgSignature sig -> BoxCoalg f -> BoxCoalg (sig.Free f)
BoxCoalgFree sigCoalg fCoalg = MkBoxCoalg $ \w, term, w', rho =>
  case term of
    Return w1 var => Return w' (fCoalg.map rho var)
    Op pos w [< arg, cont] =>
      Op pos w'
        [< (indexAll pos sigCoalg).Args.map rho arg
        ,  BoxCoalgExp .map rho cont
        ]

||| The definition of a family `f` being an algebra over a signature `sig`
public export
(.AlgebraOver) : Signature -> Family -> Type
sig.AlgebraOver f = ForAll sig $ \op =>
  (op.Arity -% f) -|> (op.Args -% f)

||| Make an algebra over `f` given the uncurried version of each operation
export
MkAlgebraOver : {sig : Signature} -> {f : Family} ->
  (ForAll sig $ \op =>
    (FamProd [< op.Arity -% f, op.Args] -|> f))
  -> sig.AlgebraOver f
MkAlgebraOver = mapPropertyWithRelevant (\op => BoxCoalgExp .curry)

||| Lift an operation interpretation into a context `gamma`
export
liftOp : {gamma, arity, args, f : Family} ->
  (BoxCoalg args) => (BoxCoalg gamma) =>
  (op : arity -% f -|> args -% f) ->
  (arity -% (gamma -% f) -|> args -% (gamma -% f))
liftOp @{argsCoalg} @{gammaCoalg} op =
  argsCoalg.swapExps . expMap op . gammaCoalg.swapExps

||| Exponetiate an algebra over a signature by a context
export
liftAlg : {sig : Signature} -> {gamma, f : Family} ->
  (sigCoalg : BoxCoalgSignature sig) =>
  (gammaCoalg : BoxCoalg gamma) =>
  sig.AlgebraOver f ->
  sig.AlgebraOver (gamma -% f)
liftAlg @{sigCoalg} alg =
  zipPropertyWithRelevant (\opSig, opCoalg, op =>
    liftOp @{opCoalg.Args} @{gammaCoalg} op
  )
  sigCoalg alg

||| A curried version of the operation for the free monad
export
curryOp :
  (sig : Signature) ->
  (f : Family) ->
  BoxCoalg f ->
  (op : OpSig) ->
  op `Elem` sig ->
  (op.Arity -% sig.Free f) -|> (op.Args -% sig.Free f)
curryOp sig f coalg op pos = BoxCoalgExp .curry (Op pos . swap)

||| The free monad over a signature is an algera for it when `f` is a presheaf
export
TermAlgebra : {sig : Signature} ->
  (f : Family) -> BoxCoalg f -> sig.AlgebraOver (sig.Free f)
TermAlgebra {sig} f coalg = tabulateElem sig $ curryOp sig f coalg

||| The unit of the monad structure of `Free`
export
pure : {sig : Signature} -> {f : Family} -> f -|> sig.Free f
pure = Return

||| `sig.Free f` is the free algebra over `sig`, and so given an algebra
||| structure over `g` and a map `f -|> g`, we can fold over it
export
(.fold) : {sig : Signature} -> {f, g : Family} ->
  sig.AlgebraOver g -> (f -|> g) -> (sig.Free f -|> g)
alg.fold env w (Return w x  ) = env w x
alg.fold env w (Op {op} pos .(w) [< arg, k]) =
  let fold = alg.fold env
      g_op = indexAll pos alg w
      folded = g_op (expMap {h = op.Arity} fold w k)
  in eval w [< folded, arg]

||| The Kleisli extension for `sig.Free`
export
(.extend) :  {sig : Signature} -> {f,g : Family} ->
  BoxCoalg g -> (f -|> sig.Free g) -> (sig.Free f -|> sig.Free g)
coalg.extend alpha = (TermAlgebra g coalg).fold alpha

||| The multiplication of the monad structure of `Free`
export
(.join) : {sig : Signature} -> {f : Family} ->
  BoxCoalg f -> sig.Free (sig.Free f) -|> sig.Free f
coalg.join = coalg.extend id

||| The Kleisli extension for `sig.Free` in context
export
(.extendStrength) :
  {sig : Signature} ->
  {gamma, f, g : Family} ->
  {gammaCoalg : BoxCoalg gamma} ->
  {fCoalg : BoxCoalg f} ->
  (sigCoalg : BoxCoalgSignature sig) =>
  BoxCoalg g ->
  (FamProd [< gamma, f] -|> sig.Free g) ->
  (FamProd [< gamma, sig.Free f] -|> sig.Free g)
gCoalg.extendStrength alpha =
  (uncurry $
    (liftAlg @{sigCoalg} @{gammaCoalg} (TermAlgebra g gCoalg)).fold
      (fCoalg.curry $ alpha . swap)
  ) . swap

infixr 1 >>==

||| Kleisli bind for `sig.Free` in context
export
(>>==) :
  {sig : Signature} ->
  {gammas : SnocList Family} ->
  {f, g : Family} ->
  (sigCoalg : BoxCoalgSignature sig) =>
  (gammaCoalgs : ForAll gammas BoxCoalg) =>
  (fCoalg : BoxCoalg f) =>
  (gCoalg : BoxCoalg g)  =>
  (FamProd gammas -|> sig.Free f) ->
  (FamProd (gammas :< f) -|> sig.Free g) ->
  (FamProd gammas -|> sig.Free g)
(>>==) xs k =
  let gammaCoalg = BoxCoalgProd $
    mapPropertyWithRelevant (\_, c => c) gammaCoalgs
  in
  ( gCoalg.extendStrength {sigCoalg} {fCoalg} {gammaCoalg}
      (\w, [< env, x] => k w (env :< x))
  ) . tuple [< id, xs]