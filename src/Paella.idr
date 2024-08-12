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

public export
infix 1 ~|>

||| Signature for a single operation, which takes an argument and has a
||| branching arity
public export
record (.opSig) p where
  constructor (~|>)
  Args  : p.family
  Arity : p.family

||| A signature is a family of operation signatures
public export
(.signature) : Type -> Type
p.signature = p.opSig -> Type

||| The free monad on families of algebraic operations
public export
data (.Free) : p.signature -> p.family -> p.family where
  ||| Embeds the family into the monad
  Return : f -|> sig.Free f
  ||| Embeds an operation into the monad
  Op : {0 opSig : p.opSig} -> {0 f : p.family} ->
    (op : sig opSig) ->
    FamProd [< opSig.Args , opSig.Arity -% sig.Free f]
    -|> sig.Free f

||| Evidence that the arguments and arity of an operation are presheaves
public export
record BoxCoalgOpSig (op : p.opSig) where
  constructor MkFunOpSig
  Args  : BoxCoalg op.Args
  Arity : BoxCoalg op.Arity

||| Evidence that the arguments and arities of all operation in a signature
||| are presheaves
public export 0
BoxCoalgSignature : p.signature -> Type
BoxCoalgSignature sig = {0 opSig : p.opSig} -> (op : sig opSig) ->
  BoxCoalgOpSig opSig

||| When the signature consists of presheaves and the family is a presheaf,
||| then the free monad is also a presheaf
export
BoxCoalgFree : {sig : p.signature} -> {f : p.family} ->
  BoxCoalgSignature sig -> BoxCoalg f -> BoxCoalg (sig.Free f)
BoxCoalgFree sigCoalg fCoalg = MkBoxCoalg $ \w, term, w', rho =>
  case term of
    Return w1 var => Return w' (fCoalg.map rho var)
    Op op w [< arg, cont] =>
      Op op w'
        [< (sigCoalg op).Args.map rho arg
        ,  BoxCoalgExp .map rho cont
        ]

||| The definition of a family `f` being an algebra over a signature `sig`
public export 0
(.AlgebraOver) : p.signature -> (0 f : p.family) -> Type
sig.AlgebraOver f = {0 opSig : p.opSig} -> (op : sig opSig) ->
  (opSig.Arity -% f) -|> (opSig.Args -% f)

||| Make an algebra over `f` given the uncurried version of each operation
export
MkAlgebraOver : {sig : p.signature} -> {0 f : p.family} ->
  ({0 opSig : p.opSig} -> (op : sig opSig) ->
    FamProd [< opSig.Arity -% f, opSig.Args] -|> f)
  -> sig.AlgebraOver f
MkAlgebraOver ops op = BoxCoalgExp .curry (ops op)

||| Lift an operation interpretation into a context `gamma`
export
liftOp : {0 gamma, arity, args, f : p.family} ->
  (BoxCoalg args) => (BoxCoalg gamma) =>
  (op : arity -% f -|> args -% f) ->
  (arity -% (gamma -% f) -|> args -% (gamma -% f))
liftOp @{argsCoalg} @{gammaCoalg} op =
  argsCoalg.swapExps . expMap op . gammaCoalg.swapExps

||| Exponetiate an algebra over a signature by a context
export
liftAlg : {sig : p.signature} -> {0 gamma, f : p.family} ->
  (sigCoalg : BoxCoalgSignature sig) =>
  (gammaCoalg : BoxCoalg gamma) =>
  sig.AlgebraOver f ->
  sig.AlgebraOver (gamma -% f)
liftAlg @{sigCoalg} alg {opSig} op =
  liftOp @{(sigCoalg op).Args} @{gammaCoalg} (alg op)

||| A curried version of the operation for the free monad
export
curryOp :
  (sig : p.signature) ->
  (0 f : p.family) ->
  BoxCoalg f ->
  {0 opSig : p.opSig} ->
  (op : sig opSig) ->
  (opSig.Arity -% sig.Free f) -|> (opSig.Args -% sig.Free f)
curryOp sig f coalg op = BoxCoalgExp .curry (Op op . swap)

||| The free monad over a signature is an algera for it when `f` is a presheaf
export
TermAlgebra : {sig : p.signature} ->
  (0 f : p.family) -> BoxCoalg f -> sig.AlgebraOver (sig.Free f)
TermAlgebra {sig} f coalg = curryOp sig f coalg

||| The unit of the monad structure of `Free`
export
pure : {sig : p.signature} -> {0 f : p.family} -> f -|> sig.Free f
pure = Return

||| `sig.Free f` is the free algebra over `sig`, and so given an algebra
||| structure over `g` and a map `f -|> g`, we can fold over it
export
(.fold) : {sig : p.signature} -> {0 f, g : p.family} ->
  sig.AlgebraOver g -> (f -|> g) -> (sig.Free f -|> g)
alg.fold env w (Return w x  ) = env w x
alg.fold env w (Op {opSig} op .(w) [< arg, k]) =
  let fold = alg.fold env
      g_op = alg op w
      folded = g_op (expMap {h = opSig.Arity} fold w k)
  in eval w [< folded, arg]

||| The Kleisli extension for `sig.Free`
export
(.extend) :  {sig : p.signature} -> {0 f,g : p.family} ->
  BoxCoalg g -> (f -|> sig.Free g) -> (sig.Free f -|> sig.Free g)
coalg.extend alpha = (TermAlgebra g coalg).fold alpha

||| The multiplication of the monad structure of `Free`
export
(.join) : {sig : p.signature} -> {f : p.family} ->
  BoxCoalg f -> sig.Free (sig.Free f) -|> sig.Free f
coalg.join = coalg.extend id

||| The Kleisli extension for `sig.Free` in context
export
(.extendStrength) :
  {sig : p.signature} ->
  {0 gamma, f, g : p.family} ->
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

export
infixr 1 >>==

||| Kleisli bind for `sig.Free` in context
export
(>>==) :
  {sig : p.signature} ->
  {0 gammas : SnocList p.family} ->
  {f, g : p.family} ->
  (sigCoalg : BoxCoalgSignature sig) =>
  (gammaCoalgs : ForAll gammas BoxCoalg) =>
  (fCoalg : BoxCoalg f) =>
  (gCoalg : BoxCoalg g)  =>
  (FamProd gammas -|> sig.Free f) ->
  (FamProd (gammas :< f) -|> sig.Free g) ->
  (FamProd gammas -|> sig.Free g)
(>>==) xs k =
  let gammaCoalg = BoxCoalgProd $
    mapProperty (\c => c) gammaCoalgs
  in
  ( gCoalg.extendStrength {sigCoalg} {fCoalg} {gammaCoalg}
      (\w, [< env, x] => k w (env :< x))
  ) . tuple [< id, xs]

------- Generic effects ----------

-- Can derive from previous but can cut out hassle
public export
abst : (f -|> g) -> (f -% g).elem
abst alpha w' w'' [< rho, x] = alpha w'' x

public export
unabst : (f -% g).elem -> (f -|> g)
unabst alpha w' x = alpha w' w' [< id, x]

public export 0
genOpType : p.signature -> p.opSig -> Type
genOpType sig opSig = opSig.Args -|> sig.Free opSig.Arity

public export
genOp : {sig : p.signature} -> {0 opSig : p.opSig} -> (op : sig opSig) -> genOpType sig opSig
genOp op w args = Op {sig} op w [< args, abst pure w]
