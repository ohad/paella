module ReverseMode

import Paella

Eq (Var a w) where
  Here      == Here      = True
  (There x) == (There y) = x == y
  _         == _         = False

splitAll : {sy, sx : SnocList _} -> All p (sy ++ sx) -> (All p sy, All p sx)
splitAll {sx = [<]} sa = (sa, [<])
splitAll {sx = _ :< _} (sa :< a) =
  let (sb, sa') = splitAll sa in (sb, sa' :< a)

joinAll : {sy, sx : SnocList _} -> All p sy -> All p sx -> All p (sy ++ sx)
joinAll {sx = [<]} sa [<] = sa
joinAll {sx = _ :< _} sa (sb :< b) = joinAll sa sb :< b

public export
IntCell : A
IntCell = Ptr

public export
ValueOf : A -> Type
ValueOf Ptr = Int

public export
TypeOf : A -> Family
TypeOf Ptr = const (ValueOf Ptr)

-- Should propagate structure more nicely
%hint
export
BoxCoalgA : (a : A) -> BoxCoalg $ TypeOf a
BoxCoalgA Ptr = BoxCoalgConst

||| Type of reading an A-cell
public export
readType : A -> OpSig
readType a = Var a ~|> TypeOf a

||| Type of writing an A-cell
writeType : A -> OpSig
writeType a = FamProd [< Var a, TypeOf a] ~|> const ()

||| Allocate a fresh cell storing an a value
public export
newType : A -> OpSig
newType a = TypeOf a ~|> Var a

||| Type of equality testing:
public export
equalType : A -> OpSig
equalType a = FamProd [< Var a, Var a] ~|> const Bool

public export
constType : (a : Family) -> OpSig
constType a = const Int ~|> a

public export
negateType : (a : Family) -> OpSig
negateType a = a ~|> a

public export
addType : (a : Family) -> OpSig
addType a = FamProd [< a, a] ~|> a

public export
multiplyType : (a : Family) -> OpSig
multiplyType a = FamProd [< a, a] ~|> a

public export
data BaseSig : Signature where
  Read     : BaseSig (readType IntCell)
  Write    : BaseSig (writeType IntCell)
  New      : BaseSig (newType IntCell)
  Equal    : BaseSig (equalType IntCell)
  Const    : BaseSig (constType (const Int))
  Negate   : BaseSig (negateType (const Int))
  Add      : BaseSig (addType (const Int))
  Multiply : BaseSig (multiplyType (const Int))

%hint
public export
BaseSigFunc : BoxCoalgSignature BaseSig
BaseSigFunc Read = 
  MkFunOpSig
    { Arity = BoxCoalgA IntCell
    , Args  = BoxCoalgVar
    }
BaseSigFunc Write =
  MkFunOpSig
    { Arity = BoxCoalgConst
    , Args = BoxCoalgProd [< BoxCoalgVar, BoxCoalgA IntCell]
    }
BaseSigFunc New =
  MkFunOpSig
    { Arity = BoxCoalgVar
    , Args = BoxCoalgA IntCell
    }
BaseSigFunc Equal =
  MkFunOpSig
    { Arity = BoxCoalgConst
    , Args = BoxCoalgProd [< BoxCoalgVar, BoxCoalgVar]
    }
BaseSigFunc Const =
  MkFunOpSig
    { Arity = BoxCoalgConst
    , Args = BoxCoalgConst
    }
BaseSigFunc Negate =
  MkFunOpSig
    { Arity = BoxCoalgConst
    , Args = BoxCoalgConst
    }
BaseSigFunc Add =
  MkFunOpSig
    { Arity = BoxCoalgConst
    , Args = BoxCoalgProd [< BoxCoalgConst, BoxCoalgConst]
    }
BaseSigFunc Multiply =
  MkFunOpSig
    { Arity = BoxCoalgConst
    , Args = BoxCoalgProd [< BoxCoalgConst, BoxCoalgConst]
    }

export
read : genOpType BaseSig (readType IntCell)
read = genOp Read

export
write : genOpType BaseSig (writeType IntCell)
write = genOp Write

export
new : genOpType BaseSig (newType IntCell)
new = genOp New

export
equal : genOpType BaseSig (equalType IntCell)
equal = genOp Equal

export
c : genOpType BaseSig (constType (const Int))
c = genOp Const

export
neg : genOpType BaseSig (negateType (const Int))
neg = genOp Negate

export
add : genOpType BaseSig (addType (const Int))
add = genOp Add

export
mul : genOpType BaseSig (multiplyType (const Int))
mul = genOp Multiply

------------ ground heap handler ---------------
StateIn : Family
StateIn w = ForAll w ValueOf

getComponent : Var a w -> StateIn w -> ValueOf a
getComponent Here (_ :< s) = s
getComponent (There pos) (ss :< _) = getComponent pos ss

setComponent : Var a w -> StateIn w -> ValueOf a -> StateIn w
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

readHeapOp : FamProd [< TypeOf IntCell -% Heap t, Var IntCell] -|> Heap t
readHeapOp w [< cont, var] ss =
  let val = getComponent var ss in
  eval w [< cont, val] ss

writeHeapOp :
  FamProd [< const () -% Heap t, FamProd [< Var IntCell, TypeOf IntCell]]
  -|> Heap t
writeHeapOp w [< cont, [< var, val]] ss =
  let ss' = setComponent var ss val in
  eval w [< cont, ()] ss'

newHeapOp :
  FamProd [< [< IntCell].shift (Heap t), TypeOf IntCell] -|> Heap t
newHeapOp w [< cont, val] ss =
  let combined = joinAll {sy = [< IntCell]} [< val] ss
      (t, ss') = cont combined
  in (t, snd (splitAll {sy = [< Ptr]} ss'))

-- The action of the injection n -> n + 1 of Inj on the heap
extendHeap : Heap t -|> [< IntCell].shift (Heap t)
extendHeap w h sv =
  let (v', sv') = splitAll {sy = [< IntCell]} sv
      (x, sv'') = h sv'
  in (x, joinAll v' sv')

-- Viewed as the right Kan extension of Heap along the inclusion Inj -> Fin
LocHeap : Type -> Family
LocHeap t w = (w' : World) -> (w ~> w') -> Heap t w'

runLocHeap : (w' : World) -> (w ~> w') -> LocHeap t w ->
  StateIn w' -> Pair t (StateIn w')
runLocHeap w' rho h s = h w' rho s

extractHeap : LocHeap t -|> Heap t
extractHeap w = runLocHeap w id

-- LocHeap is a presheaf
LocHeapCoalg : {t : Type} -> BoxCoalg (LocHeap t)
LocHeapCoalg = MkBoxCoalg $ \w, h, w'', rho => \w', rho' => h w' (rho' . rho)

readLocHeapOp : {t : Type} ->
  FamProd [< TypeOf IntCell -% LocHeap t, Var IntCell] -|> LocHeap t
readLocHeapOp w [< cont, var] w' rho =
  let var' = BoxCoalgVar .map rho var
      cont' = expMap extractHeap w' (BoxCoalgExp .map rho cont)
  in readHeapOp w' [< cont', var']

writeLocHeapOp : {t : Type} ->
  FamProd [< const () -% LocHeap t, FamProd [< Var IntCell, TypeOf IntCell]]
  -|> LocHeap t
writeLocHeapOp w [< cont, [< var, val]] w' rho =
  let var' = BoxCoalgVar .map rho var
      cont' = expMap extractHeap w' (BoxCoalgExp .map rho cont)
  in writeHeapOp w' [< cont', [< var', val]]

newLocHeapOp : {t : Type} ->
  FamProd [< Var IntCell -% LocHeap t, TypeOf IntCell] -|> LocHeap t
newLocHeapOp w [< cont, val] w' rho =
  let rho' = bimap {w1 = [< Ptr], w1' = [< Ptr]} id rho
      cont' = cont ([< Ptr] ++ w) [< inr, swapRen Ptr Here] ([< Ptr] ++ w') rho'
  in newHeapOp w' [< cont', val]

equalLocHeapOp : {t : Type} ->
  FamProd [< const Bool -% LocHeap t, FamProd [< Var IntCell, Var IntCell]]
  -|> LocHeap t
equalLocHeapOp w [< cont, [< var1, var2]] w' rho =
  let var1' = BoxCoalgVar .map rho var1
      var2' = BoxCoalgVar .map rho var2
      cont' = expMap extractHeap w' (BoxCoalgExp .map rho cont)
  in eval w' [< cont', var1' == var2']

constLocHeapOp : {t : Type} ->
  FamProd [< const Int -% LocHeap t, const Int] -|> LocHeap t
constLocHeapOp w [< cont, c] w' rho = cont w [<id, c] w' rho

negateLocHeapOp : {t : Type} ->
  FamProd [< const Int -% LocHeap t, const Int] -|> LocHeap t
negateLocHeapOp w [< cont, x] w' rho = cont w [<id, Prelude.negate x] w' rho

addLocHeapOp : {t : Type} ->
  FamProd [< const Int -% LocHeap t, FamProd [< const Int, const Int] ] -|> 
  LocHeap t
addLocHeapOp w [< cont, [< x, y]] w' rho = cont w [<id, x + y] w' rho

multiplyLocHeapOp : {t : Type} ->
  FamProd [< const Int -% LocHeap t, FamProd [< const Int, const Int] ] -|> 
  LocHeap t
multiplyLocHeapOp w [< cont, [< x, y]] w' rho = cont w [<id, x * y] w' rho

LocHeapAlgebra :  {t : Type} -> BaseSig .AlgebraOver (LocHeap t)
LocHeapAlgebra = MkAlgebraOver {sig = BaseSig} $ \case
  Read     => readLocHeapOp
  Write    => writeLocHeapOp
  New      => newLocHeapOp
  Equal    => equalLocHeapOp
  Const    => constLocHeapOp
  Negate   => negateLocHeapOp
  Add      => addLocHeapOp
  Multiply => multiplyLocHeapOp

-- The unit of the local state monad gave pureHeap, this is the right Kan
-- extension of Inj -> Fin applied to it. Thus, this is the needed algebra.
pureLocHeap : t -> LocHeap t w
pureLocHeap t w rho = pureHeap t

-- l1 := !l2
readWrite : FamProd [< Var IntCell, Var IntCell] -|> BaseSig .Free (const Unit)
readWrite =
                             (\w, [< l1, l2]       =>
  read _ l2           ) >>== (\w, [< l1, l2, val ] =>
  write _ [< l1, val] )

-- swap value of two locations with temp location
swap : FamProd [< Var IntCell, Var IntCell] -|> BaseSig .Free (const Unit)
swap =
                                (\w, [< l1, l2]              =>
  new _ 0                ) >>== (\w, [< l1, l2, lt]          =>
  readWrite _ [< lt, l1] ) >>== (\w, [< l1, l2, lt, () ]     =>
  readWrite _ [< l1, l2] ) >>== (\w, [< l1, l2, lt, (), () ] =>
  readWrite _ [< l2, lt] )

handle : BaseSig .Free (const Unit) -|> LocHeap Unit
handle w comp = LocHeapAlgebra .fold
  {g = LocHeap _}
  (\w, x => pureLocHeap x) w comp

Ex : (Unit, StateIn [< IntCell, IntCell])
Ex = handle [< Ptr, Ptr] (
    ReverseMode.swap [< Ptr, Ptr] [< Here, There Here]
  ) [< Ptr, Ptr] id [< 1, 2]