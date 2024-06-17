module ReverseMode

import Paella
import Debug.Trace

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

Show (StateIn w) where
  show [<] = ""
  show (sy :< y) = "*" ++ show sy

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
  let val = traceVal $ getComponent var ss in
  eval w [< cont, val] ss

writeHeapOp :
  FamProd [< const () -% Heap t, FamProd [< Var IntCell, TypeOf IntCell]]
  -|> Heap t
writeHeapOp w [< cont, [< var, val]] ss =
  let ss' = setComponent var ss (traceVal val) in
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

handle : {t : Type} -> BaseSig .Free (const t) -|> LocHeap t
handle w comp = LocHeapAlgebra .fold
  {g = LocHeap _}
  (\w, x => pureLocHeap x) w comp

Ex1 : (Unit, StateIn [< IntCell, IntCell])
Ex1 = handle [< Ptr, Ptr] (
    ReverseMode.swap [< Ptr, Ptr] [< Here, There Here]
  ) [< Ptr, Ptr] id [< 1, 2]

-- 1 + x^3 + (- y^2)
term : FamProd [< const Int, const Int] -|> BaseSig .Free (const Int)
term =                   (\w, [< x, y] =>
 c _ 1            ) >>== (\w, [< x, y, o] =>
 mul _ [< x, x]   ) >>== (\w, [< x, y, o, x2] =>
 mul _ [< x, x2]  ) >>== (\w, [< x, y, o, x2, x3] =>
 add _ [< o, x3]  ) >>== (\w, [< x, y, o, x2, x3, p] =>
 mul _ [< y, y]   ) >>== (\w, [< x, y, o, x2, x3, p, y2] =>
 neg _ y2         ) >>== (\w, [< x, y, o, x2, x3, p, y2, ny2] =>
 add _ [< p, ny2] )

Ex2 : (Int, StateIn [< ])
Ex2 = handle [< ] (
    term [< ] [< 2, 4]
  ) [< ] id [< ]

------------------------ Reverse mode ------------------------

export
Prop : Family
Prop = FamProd [< const Int, Var IntCell]

%hint
BoxCoalgProp : BoxCoalg Prop
BoxCoalgProp = BoxCoalgProd [< BoxCoalgConst, BoxCoalgVar]

public export
data RSig : Signature where
  RWrite    : RSig (writeType IntCell)
  RConst    : RSig (constType Prop)
  RNegate   : RSig (negateType Prop)
  RAdd      : RSig (addType Prop)
  RMultiply : RSig (multiplyType Prop)

%hint
public export
RSigFunc : BoxCoalgSignature RSig
RSigFunc RWrite =
  MkFunOpSig
    { Arity = BoxCoalgConst
    , Args = BoxCoalgProd [< BoxCoalgVar, BoxCoalgA IntCell]
    }
RSigFunc RConst =
  MkFunOpSig
    { Arity = BoxCoalgProp
    , Args = BoxCoalgConst
    }
RSigFunc RNegate =
  MkFunOpSig
    { Arity = BoxCoalgProp
    , Args = BoxCoalgProp
    }
RSigFunc RAdd =
  MkFunOpSig
    { Arity = BoxCoalgProp
    , Args = BoxCoalgProd [< BoxCoalgProp, BoxCoalgProp]
    }
RSigFunc RMultiply =
  MkFunOpSig
    { Arity = BoxCoalgProp
    , Args = BoxCoalgProd [< BoxCoalgProp, BoxCoalgProp]
    }

export
rwrite : genOpType RSig (writeType IntCell)
rwrite = genOp RWrite

export
rc : genOpType RSig (constType Prop)
rc = genOp RConst

export
rneg : genOpType RSig (negateType Prop)
rneg = genOp RNegate

export
radd : genOpType RSig (addType Prop)
radd = genOp RAdd

export
rmul : genOpType RSig (multiplyType Prop)
rmul = genOp RMultiply

BoxCoalgBaseFree : {f : Family} -> BoxCoalg f -> BoxCoalg (BaseSig .Free f)
BoxCoalgBaseFree = BoxCoalgFree BaseSigFunc

%hint
BoxCoalgExpBaseFree : BoxCoalg (g -% BaseSig .Free f)
BoxCoalgExpBaseFree = BoxCoalgExp

%hint
BoxCoalgVarType : BoxCoalg (FamProd [< Var IntCell, TypeOf IntCell])
BoxCoalgVarType = BoxCoalgProd [< BoxCoalgVar, BoxCoalgA IntCell]

%hint
BoxCoalgPropProp : BoxCoalg (FamProd [< Prop, Prop])
BoxCoalgPropProp = BoxCoalgProd [< BoxCoalgProp, BoxCoalgProp]

writeBaseSigOp :
  FamProd [< const () -% BaseSig .Free (const ()), FamProd [< Var IntCell, TypeOf IntCell]]
  -|> BaseSig .Free (const ())
writeBaseSigOp =           (\w, [< cont, [< l, v]] =>
  trace "WRITE" $ write _ [< l, v]  ) >>== (\w, [< cont, [< l, v], ()] =>
  cont _ [< id, ()] )

constBaseSigOp :
  FamProd [< Prop -% BaseSig .Free (const ()), const Int] -|>
  BaseSig .Free (const ())
constBaseSigOp =                 (\w, [< cont, c] =>
  new _ 0                 ) >>== (\w, [< cont, c, l] =>
  cont _ [< id, [< c, l]] )

negateBaseSigOp :
  FamProd [< Prop -% BaseSig .Free (const ()), Prop] -|>
  BaseSig .Free (const ())
negateBaseSigOp =                 (\w, [< cont, [< v, dv]] =>
  new _ 0                  ) >>== (\w, [< cont, [< v, dv], dr] =>
  neg _ v                  ) >>== (\w, [< cont, [< v, dv], dr, r] =>
  cont _ [< id, [< r, dr]] ) >>>> (\w, [< cont, [< v, dv], dr, r] =>
  read _ dr                ) >>== (\w, [< cont, [< v, dv], dr, r, dr'] =>
  read _ dv                ) >>== (\w, [< cont, [< v, dv], dr, r, dr', dv'] =>
  neg _ dr'                ) >>== (\w, [< cont, [< v, dv], dr, r, dr', dv', dr''] =>
  add _ [< dv', dr']       ) >>== (\w, [< cont, [< v, dv], dr, r, dr', dv', dr'', dv''] =>
  write _ [< dv, dv'']     )

addBaseSigOp :
  FamProd [< Prop -% BaseSig .Free (const ()), FamProd [< Prop, Prop] ] -|>
  BaseSig .Free (const ())
addBaseSigOp =                    (\w, [< cont, [< [< x, dx], [< y, dy ]] ] =>
  new _ 0                  ) >>== (\w, [< cont, [< [< x, dx], [< y, dy ]], dr] =>
  add _ [< x, y]           ) >>== (\w, [< cont, [< [< x, dx], [< y, dy ]], dr, r] =>
  cont _ [< id, [< r, dr]] ) >>>> (\w, [< cont, [< [< x, dx], [< y, dy ]], dr, r] =>
  read _ dr                ) >>== (\w, [< cont, [< [< x, dx], [< y, dy ]], dr, r, dr'] =>
  read _ dx                ) >>== (\w, [< cont, [< [< x, dx], [< y, dy ]], dr, r, dr', dx'] =>
  read _ dy                ) >>== (\w, [< cont, [< [< x, dx], [< y, dy ]], dr, r, dr', dx', dy'] =>
  add _ [< dx', dr']       ) >>== (\w, [< cont, [< [< x, dx], [< y, dy ]], dr, r, dr', dx', dy', dx''] =>
  add _ [< dy', dr']       ) >>== (\w, [< cont, [< [< x, dx], [< y, dy ]], dr, r, dr', dx', dy', dx'', dy''] =>
  write _ [< dx, dx'']     ) >>>> (\w, [< cont, [< [< x, dx], [< y, dy ]], dr, r, dr', dx', dy', dx'', dy''] =>
  write _ [< dy, dy'']     )

multiplyBaseSigOp :
  FamProd [< Prop -% BaseSig .Free (const ()), FamProd [< Prop, Prop] ] -|>
  BaseSig .Free (const ())
multiplyBaseSigOp =               (\w, [< cont, [< [< x, dx], [< y, dy ]] ] =>
  trace "n1"  $ new _ 0                  ) >>== (\w, [< cont, [< [< x, dx], [< y, dy ]], dr] =>
  trace "a2"  $ mul _ [< traceVal x, traceVal y]           ) >>== (\w, [< cont, [< [< x, dx], [< y, dy ]], dr, r] =>
  trace "c3"  $ cont _ [< id, [< traceVal r, dr]] ) >>>> (\w, [< cont, [< [< x, dx], [< y, dy ]], dr, r] =>
  trace "r4"  $ read _ dr                ) >>== (\w, [< cont, [< [< x, dx], [< y, dy ]], dr, r, dr'] =>
  trace "r5"  $ read _ dx                ) >>== (\w, [< cont, [< [< x, dx], [< y, dy ]], dr, r, dr', dx'] =>
  trace "r6"  $ read _ dy                ) >>== (\w, [< cont, [< [< x, dx], [< y, dy ]], dr, r, dr', dx', dy'] =>
  trace "m7"  $ mul _ [< y, traceVal dr']         ) >>== (\w, [< cont, [< [< x, dx], [< y, dy ]], dr, r, dr', dx', dy', dx''] =>
  trace "a8"  $ add _ [< traceVal dx', traceVal dx'']      ) >>== (\w, [< cont, [< [< x, dx], [< y, dy ]], dr, r, dr', dx', dy', dx'', dx'''] =>
  trace "m9"  $ mul _ [< x, dr']         ) >>== (\w, [< cont, [< [< x, dx], [< y, dy ]], dr, r, dr', dx', dy', dx'', dx''', dy''] =>
  trace "a10" $ add _ [< traceVal dy', traceVal dy'']      ) >>== (\w, [< cont, [< [< x, dx], [< y, dy ]], dr, r, dr', dx', dy', dx'', dx''', dy'', dy'''] =>
  trace "w11" $ write _ [< dx, traceVal dx''']    ) >>>> (\w, [< cont, [< [< x, dx], [< y, dy ]], dr, r, dr', dx', dy', dx'', dx''', dy'', dy'''] =>
  trace "w12" $ write _ [< dy, traceVal dy''']    )

BaseSigAlgebra :  RSig .AlgebraOver (BaseSig .Free (const ()))
BaseSigAlgebra = MkAlgebraOver {sig = RSig} $ \case
  RWrite    => writeBaseSigOp
  RConst    => constBaseSigOp
  RNegate   => negateBaseSigOp
  RAdd      => addBaseSigOp
  RMultiply => multiplyBaseSigOp

-- 1 + x^3 + (- y^2)
rterm : FamProd [< Prop, Prop] -|> RSig .Free Prop
rterm =                   (\w, [< x, y] =>
 rc _ 1            ) >>== (\w, [< x, y, o] =>
 rmul _ [< x, x]   ) >>== (\w, [< x, y, o, x2] =>
 rmul _ [< x, x2]  ) >>== (\w, [< x, y, o, x2, x3] =>
 radd _ [< o, x3]  ) >>== (\w, [< x, y, o, x2, x3, p] =>
 rmul _ [< y, y]   ) >>== (\w, [< x, y, o, x2, x3, p, y2] =>
 rneg _ y2         ) >>== (\w, [< x, y, o, x2, x3, p, y2, ny2] =>
 radd _ [< p, ny2] )

crterm : FamProd [< Prop] -|> RSig .Free Prop
crterm =                 (\w, [< x] =>
  rc _ 4          ) >>== (\w, [< x, c] =>
  rterm _ [< x, c])

squared : FamProd [< Prop] -|> RSig .Free (const ())
squared = (\w, [< x] => rmul _ [< x, x]) >>== (\w, [< x, [< _, dy]] =>  rwrite _ [< dy, 1])

rhandle : RSig .Free (const ()) -|> BaseSig .Free (const ())
rhandle w comp = BaseSigAlgebra .fold
  {g = BaseSig .Free (const ())}
  pure w comp

aux : RSig .Free Prop -|> RSig .Free (const ())
aux = BoxCoalgConst .extend (\w, [< _, dx] => rwrite w [< dx, 1])

grad : (FamProd [< Prop] -|> RSig .Free (const ())) ->
  (FamProd [< const Int] -|> BaseSig .Free (const Int))
grad f =                                      (\w, [< x]  =>
  new _ 0   )                            >>== (\w, [< x, dx] =>
  rhandle w (f w [< [< x, dx]])) >>>> (\w, [< x, dx] =>
  read _ dx )

main : IO ()
main =
  let (r, _) = handle [<] (grad squared [<] [< 3]) [<] id [<]
  in print r