module LocalState

import Paella

export
infix 3 !!, ::=, ?!

public export
ConsCell : A
ConsCell = P

public export
-- Postulate: each parameter has a type
-- For now, just cons cells
TypeOf : A -> Family
TypeOf P = FamProd [< const String, Var ConsCell]

%hint
public export
BoxCoalgA : (a : A) -> BoxCoalg $ TypeOf a
-- Should propagate structure more nicely
BoxCoalgA P = BoxCoalgProd $ [< BoxCoalgConst, BoxCoalgVar]

public export
||| Type of reading an A-cell
readType : A -> OpSig
readType a = Var a ~|> TypeOf a

public export
||| Type of writing an a
||| w_0 : [a, []]
writeType : A -> OpSig
writeType a = FamProd [< Var a, TypeOf a] ~|> const ()

public export
||| Allocate a fresh cell storing an a value
newType : A -> OpSig
newType a = [< a].shift (TypeOf a) ~|> Var a

public export
data LSSig : Signature where
  Read  : LSSig (readType  ConsCell)
  Write : LSSig (writeType ConsCell)
  New   : LSSig (newType   ConsCell)

%hint
public export
LSSigFunc : BoxCoalgSignature LSSig
LSSigFunc Read = MkFunOpSig
  { Arity = BoxCoalgProd [< BoxCoalgConst, BoxCoalgVar]
  , Args = BoxCoalgVar
  }
LSSigFunc Write = MkFunOpSig
  { Arity = BoxCoalgConst
  , Args = BoxCoalgProd [< BoxCoalgVar, BoxCoalgA ConsCell]
  }
LSSigFunc New = MkFunOpSig
  { Arity = BoxCoalgVar
  , Args = [< ConsCell].shiftCoalg (BoxCoalgA ConsCell)
  }

public export
read : genOpType LSSig (readType ConsCell)
read = genOp Read

public export
write : genOpType LSSig (writeType ConsCell)
write = genOp Write

public export
new : genOpType LSSig (newType ConsCell)
new = genOp New

---- The heap handler ----------------

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
  mapPropertyWithRelevant'
    (\a => (BoxCoalgA a).map rho)
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
  let u = mapToProperty $ (HeapletCoalg {shape = w'}).map
           (inr {w1 = w}) heap
      v = mapToProperty init
     -- Probably terrible performance, but meh
  in propertyToMap (v ++ u)

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
  , val = coalg.map (Paella.Worlds.bimap id rho) hidden.val
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
LSHandlerPsh coalg = BoxCoalgExp

public export
val : {f : Family} -> {coalg : BoxCoalg f} ->
  coalg =|> (LSHandlerPsh coalg)
val = coalg.curry $ \w, [< v, heap] =>
  Private.pure {f} w v

public export
-- Heap's LSAlgebra structure
LSalg : {f : Family} -> {coalg : BoxCoalg f} ->
  LSSig .AlgebraOver (LSHandlerCarrier f)
LSalg = MkAlgebraOver {sig = LSSig} $ \case
  Read  =>
    \roots, [< kont, loc], shape, [< rho, heap] =>
    let result = heap !! (rho _ loc)
    in eval shape [< kont shape [< rho , result] , heap]
  Write =>
    \roots, [< kont, [<loc, newval]], shape, [< rho, heap] =>
    let newHeap = heap.update
                  (rho _ loc ::=
                     (BoxCoalgA ConsCell).map rho newval)
    in eval shape [< kont shape [< rho , ()] , newHeap]
  New   =>
    \roots, [< kont, newval], shape, [< rho, heap] =>
      let newheap : Heap ([< ConsCell] ++ shape)
                  := extendHeap {w = [< ConsCell]} shape
                     [< heap , [<
                        (BoxCoalgA ConsCell).map
                          (Paella.Worlds.bimap id rho)
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
                          ([< id, newheap])
      in hide result

public export
handle :
  LSSig .Free (const $ List String) [<] ->
  Private (const (List String)) [<]
handle comp =
  let coalg = MkBoxCoalg (\w, strs, b, f => strs)
  in (LSalg {coalg}).fold (val {coalg}) [<] comp [<] [< id,[<]]
