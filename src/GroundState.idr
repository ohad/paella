module GroundState

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
IntCell = P

public export
ValueOf : A -> Type
ValueOf P = Int

public export
TypeOf : A -> Family
TypeOf P = const (ValueOf P)

-- Should propagate structure more nicely
%hint
export
BoxCoalgA : (a : A) -> BoxCoalg $ TypeOf a
BoxCoalgA P = BoxCoalgConst

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
data LSSig : Signature where
  Read  : LSSig (readType IntCell)
  Write : LSSig (writeType IntCell)
  New   : LSSig (newType IntCell)
  Equal : LSSig (equalType IntCell)


%hint
public export
LSSigFunc : BoxCoalgSignature LSSig
LSSigFunc Read  =  MkFunOpSig
                { Arity = BoxCoalgA IntCell
                , Args  = BoxCoalgVar
                }
LSSigFunc Write = MkFunOpSig
                { Arity = BoxCoalgConst
                , Args = BoxCoalgProd
                      [< BoxCoalgVar
                       , BoxCoalgA IntCell]
                }
LSSigFunc New   = MkFunOpSig
                { Arity = BoxCoalgVar
                , Args = BoxCoalgA IntCell
                }
LSSigFunc Equal = MkFunOpSig
                { Arity = BoxCoalgConst
                , Args = BoxCoalgProd [< BoxCoalgVar, BoxCoalgVar]
                }

export
read : genOpType LSSig (readType IntCell)
read = genOp Read

export
write : genOpType LSSig (writeType IntCell)
write = genOp Write

export
new : genOpType LSSig (newType IntCell)
new = genOp New

export
equal : genOpType LSSig (equalType IntCell)
equal = genOp Equal

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
  in (t, snd (splitAll {sy = [<P]} ss'))

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
  let rho' = bimap {w1 = [< P], w1' = [< P]} id rho
      cont' = cont ([< P] ++ w) [< inr, swapRen P Here] ([< P] ++ w') rho'
  in newHeapOp w' [< cont', val]

equalLocHeapOp : {t : Type} ->
  FamProd [< const Bool -% LocHeap t, FamProd [< Var IntCell, Var IntCell]]
  -|> LocHeap t
equalLocHeapOp w [< cont, [< var1, var2]] w' rho =
  let var1' = BoxCoalgVar .map rho var1
      var2' = BoxCoalgVar .map rho var2
      cont' = expMap extractHeap w' (BoxCoalgExp .map rho cont)
  in eval w' [< cont', var1' == var2']

LocHeapAlgebra : {t : Type} -> LSSig .AlgebraOver (LocHeap t)
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
readWrite : FamProd [< Var IntCell, Var IntCell] -|> LSSig .Free (const Unit)
readWrite =
                             (\w, [< l1, l2]       =>
  read _ l2           ) >>== (\w, [< l1, l2, val ] =>
  write _ [< l1, val] )

-- swap value of two locations with temp location
swap : FamProd [< Var IntCell, Var IntCell] -|> LSSig .Free (const Unit)
swap =
                                (\w, [< l1, l2]              =>
  new _ 0                ) >>== (\w, [< l1, l2, lt]          =>
  readWrite _ [< lt, l1] ) >>== (\w, [< l1, l2, lt, () ]     =>
  readWrite _ [< l1, l2] ) >>== (\w, [< l1, l2, lt, (), () ] =>
  readWrite _ [< l2, lt] )

handle : LSSig .Free (const Unit) -|> LocHeap Unit
handle w comp = LocHeapAlgebra .fold
  {g = LocHeap _}
  (\w, _ => pureLocHeap ()) w comp

Ex : (Unit, StateIn [< IntCell, IntCell])
Ex = handle [< P, P] (
    GroundState.swap [< P, P] [< Here, There Here]
  ) [< P, P] id [< 1, 2]
