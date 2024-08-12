module GroundState

import Paella

Eq (Var a w) where
  Here      == Here      = True
  (There x) == (There y) = x == y
  _         == _         = False

splitAll : {0 sy : SnocList _} -> {sx : SnocList _} -> All p (sy ++ sx) -> (All p sy, All p sx)
splitAll {sx = [<]} sa = (sa, [<])
splitAll {sx = _ :< _} (sa :< a) =
  let (sb, sa') = splitAll sa in (sb, sa' :< a)

joinAll : {0 sy, sx : SnocList _} -> All p sy -> All p sx -> All p (sy ++ sx)
joinAll {sx = [<]} sa [<] = sa
joinAll {sx = _ :< _} sa (sb :< b) = joinAll sa sb :< b

data Cell = Ptr

public export
ValueOf : Cell -> Type
ValueOf Ptr = Int

total
public export
TypeOf : Cell -> Cell .family
TypeOf a = const (ValueOf a)

-- Should propagate structure more nicely
%hint
export
BoxCoalgA : (a : Cell) -> BoxCoalg $ TypeOf a
BoxCoalgA Ptr = BoxCoalgConst

||| Type of reading an A-cell
public export
readType : Cell -> Cell .opSig
readType a = Var a ~|> TypeOf a

0
||| Type of writing an A-cell
writeType : Cell -> Cell .opSig
writeType a = FamProd [< Var a, TypeOf a] ~|> const ()

||| Allocate a fresh cell storing an a value
public export
newType : Cell -> Cell .opSig
newType a = TypeOf a ~|> Var a

||| Type of equality testing:
public export 0
equalType : Cell -> Cell .opSig
equalType a = FamProd [< Var a, Var a] ~|> const Bool

public export
data LSSig : Cell .signature where
  Read  : {a : Cell} -> LSSig (readType a)
  Write : {a : Cell} -> LSSig (writeType a)
  New   : {a : Cell} -> LSSig (newType a)
  Equal : {a : Cell} -> LSSig (equalType a)

%hint
public export
LSSigFunc : BoxCoalgSignature LSSig
LSSigFunc Read  =  MkFunOpSig
                { Arity = BoxCoalgA _
                , Args  = BoxCoalgVar
                }
LSSigFunc Write = MkFunOpSig
                { Arity = BoxCoalgConst
                , Args = BoxCoalgProd
                      [< BoxCoalgVar
                       , BoxCoalgA _]
                }
LSSigFunc New   = MkFunOpSig
                { Arity = BoxCoalgVar
                , Args = BoxCoalgA _
                }
LSSigFunc Equal = MkFunOpSig
                { Arity = BoxCoalgConst
                , Args = BoxCoalgProd [< BoxCoalgVar, BoxCoalgVar]
                }

export
read : {a : Cell} -> genOpType LSSig (readType a)
read = genOp Read

export
write : {a : Cell} -> genOpType LSSig (writeType a)
write = genOp Write

export
new : {a : Cell} -> genOpType LSSig (newType a)
new = genOp New

export
equal : {a : Cell} -> genOpType LSSig (equalType a)
equal = genOp Equal

------------ ground heap handler ---------------
StateIn : Cell .family
StateIn w = ForAll w ValueOf

getComponent : Var a w -> StateIn w -> ValueOf a
getComponent Here (_ :< s) = s
getComponent (There pos) (ss :< _) = getComponent pos ss

setComponent : Var a w -> StateIn w -> ValueOf a -> StateIn w
setComponent Here (ss :< _) s' = ss :< s'
setComponent (There pos) (ss :< s) s' = setComponent pos ss s' :< s

-- Viewed as in Inj-presheaf, free Inj-LS algebra on the presheaf which is
-- constantly t
Heap : Type -> Cell .family
Heap t w = StateIn w -> Pair t (StateIn w)

pureHeap : t -> Heap t w
pureHeap t = \x => (t, x)

runHeap : Heap t w -> StateIn w -> Pair t (StateIn w)
runHeap h ss = h ss

readHeapOp : FamProd [< TypeOf a -% Heap t, Var a] -|> Heap t
readHeapOp w [< cont, var] ss =
  let val = getComponent var ss in
  eval w [< cont, val] ss

writeHeapOp :
  FamProd [< const () -% Heap t, FamProd [< Var a, TypeOf a]]
  -|> Heap t
writeHeapOp w [< cont, [< var, val]] ss =
  let ss' = setComponent var ss val in
  eval w [< cont, ()] ss'

newHeapOp :
  FamProd [< [< a].shift (Heap t), TypeOf a] -|> Heap t
newHeapOp w [< cont, val] ss =
  let combined = joinAll {sy = [< a]} [< val] ss
      (t, ss') = cont combined
  in (t, snd (splitAll {sy = [< a]} ss'))

-- The action of the injection n -> n + 1 of Inj on the heap
extendHeap : Heap t -|> [< a].shift (Heap t)
extendHeap w h sv =
  let (v', sv') = splitAll {sy = [< a]} sv
      (x, sv'') = h sv'
  in (x, joinAll v' sv')

-- Viewed as the right Kan extension of Heap along the inclusion Inj -> Fin
0
LocHeap : Type -> Cell .family
LocHeap t w = (w' : Cell .world) -> (w ~> w') -> Heap t w'

runLocHeap : (w' : Cell .world) -> (w ~> w') -> LocHeap t w ->
  StateIn w' -> Pair t (StateIn w')
runLocHeap w' rho h s = h w' rho s

extractHeap : LocHeap t -|> Heap t
extractHeap w = runLocHeap w id

-- LocHeap is a presheaf
LocHeapCoalg : {t : Type} -> BoxCoalg (LocHeap t)
LocHeapCoalg = MkBoxCoalg $ \w, h, w'', rho => \w', rho' => h w' (rho' . rho)

readLocHeapOp : {0 t : Type} ->
  FamProd [< TypeOf a -% LocHeap t, Var a] -|> LocHeap t
readLocHeapOp w [< cont, var] w' rho =
  let var' = BoxCoalgVar .map rho var
      cont' = expMap extractHeap w' (BoxCoalgExp .map rho cont)
  in readHeapOp w' [< cont', var']

writeLocHeapOp : {0 t : Type} ->
  FamProd [< const () -% LocHeap t, FamProd [< Var a, TypeOf a]]
  -|> LocHeap t
writeLocHeapOp w [< cont, [< var, val]] w' rho =
  let var' = BoxCoalgVar .map rho var
      cont' = expMap extractHeap w' (BoxCoalgExp .map rho cont)
  in writeHeapOp w' [< cont', [< var', val]]

newLocHeapOp : {0 t : Type} -> {a : Cell} ->
  FamProd [< Var a -% LocHeap t, TypeOf a] -|> LocHeap t
newLocHeapOp w [< cont, val] w' rho =
  let rho' = bimap {w1 = [< a], w1' = [< a]} id rho
      cont' = cont ([< a] ++ w) [< inr, swapRen a Here]
                   ([< a] ++ w') rho'
  in newHeapOp w' [< cont', val]

equalLocHeapOp : {0 t : Type} ->
  FamProd [< const Bool -% LocHeap t, FamProd [< Var a, Var a]]
  -|> LocHeap t
equalLocHeapOp w [< cont, [< var1, var2]] w' rho =
  let var1' = BoxCoalgVar .map rho var1
      var2' = BoxCoalgVar .map rho var2
      cont' = expMap extractHeap w' (BoxCoalgExp .map rho cont)
  in eval w' [< cont', var1' == var2']

LocHeapAlgebra : {0 t : Type} -> LSSig .AlgebraOver (LocHeap t)
LocHeapAlgebra = MkAlgebraOver {sig = LSSig} $ \case
  Read  => readLocHeapOp
  Write => writeLocHeapOp
  New   => newLocHeapOp
  Equal => equalLocHeapOp

-- The unit of the local state monad gave pureHeap, this is the right Kan
-- extension of Inj -> Fin applied to it. Thus, this is the needed algebra.
pureLocHeap : t -> LocHeap t w
pureLocHeap t w rho = pureHeap t

-- l1 := !l2
readWrite : {a : Cell} ->
            FamProd [< Var a, Var a] -|> LSSig .Free (const Unit)
readWrite =
                             (\w, [< l1, l2]       =>
  read _ l2           ) >>== (\w, [< l1, l2, val ] =>
  write _ [< l1, val] )

-- swap value of two locations with temp location
swap : FamProd [< Var Ptr, Var Ptr] -|> LSSig .Free (const Unit)
swap =
                                (\w, [< l1, l2]              =>
  new {a = Ptr}
            _ 0          ) >>== (\w, [< l1, l2, lt]          =>
  readWrite _ [< lt, l1] ) >>== (\w, [< l1, l2, lt, () ]     =>
  readWrite _ [< l1, l2] ) >>== (\w, [< l1, l2, lt, (), () ] =>
  readWrite _ [< l2, lt] )

handle : LSSig .Free (const Unit) -|> LocHeap Unit
handle w comp = LocHeapAlgebra .fold
  {g = LocHeap _}
  (\w, _ => pureLocHeap ()) w comp


Ex : (Unit, StateIn [< Ptr, Ptr])
Ex = handle [< Ptr, Ptr] (
    GroundState.swap [< Ptr, Ptr] [< Here, There Here]
  ) [< Ptr, Ptr] id [< 1, 2]
