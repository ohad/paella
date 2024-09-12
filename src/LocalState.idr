module LocalState

import Paella

export
infix 3 !!, ::=, ?!

data Cell = ABool | ConsCell

public export
-- Postulate: each parameter has a type
-- For now, just cons cells
0
TypeOf : Cell -> Cell .family
TypeOf ABool    = const Bool
TypeOf ConsCell = FamProd [< const String, Var ConsCell]

%hint
public export
BoxCoalgCell : (a : Cell) -> BoxCoalg $ TypeOf a
-- Should propagate structure more nicely
BoxCoalgCell ABool = BoxCoalgConst
BoxCoalgCell ConsCell = BoxCoalgProd $ [< BoxCoalgConst, BoxCoalgVar]

public export 0
||| Type of reading an A-cell
readType : Cell -> Cell .opSig
readType a = Var a ~|> TypeOf a

public export 0
||| Type of writing an a
||| w_0 : [a, []]
writeType : Cell -> Cell .opSig
writeType a = FamProd [< Var a, TypeOf a] ~|> const ()

public export 0
||| Allocate a fresh cell storing an a value
newType : Cell -> Cell .opSig
newType a = [< a].shift (TypeOf a) ~|> Var a

public export
data LSSig : Cell .signature where
  Read  : {a : Cell} -> LSSig (readType  a)
  Write : {a : Cell} -> LSSig (writeType a)
  New   : {a : Cell} -> LSSig (newType a)

%hint
public export
LSSigFunc : BoxCoalgSignature LSSig
LSSigFunc (Read  {a}) = MkFunOpSig
  { Arity = BoxCoalgCell a
  , Args  = BoxCoalgVar
  }
LSSigFunc (Write {a}) = MkFunOpSig
  { Arity = BoxCoalgConst
  , Args = BoxCoalgProd [< BoxCoalgVar, BoxCoalgCell a]
  }
LSSigFunc (New   {a}) = MkFunOpSig
  { Arity = BoxCoalgVar
  , Args = [< a].shiftCoalg (BoxCoalgCell a)
  }

public export
read : {a : Cell} -> genOpType LSSig (readType a)
read = genOp Read

public export
write : {a : Cell} -> genOpType LSSig (writeType a)
write = genOp Write

public export
new : {a : Cell} -> genOpType LSSig (newType a)
new = genOp New

---- The heap handler ----------------

public export 0
Heaplet : (shape : Cell .world) -> Cell .family
Heaplet shape = FamProd (map TypeOf shape)

public export
(!!) : Heaplet shape w -> Var a shape ->
  TypeOf a w
(h :< x) !! Here = x
[<]      !! (There pos) impossible
(h :< x) !! (There pos) = h !! pos

public export
record Update (a : Cell) (shape, w : Cell .world) where
  constructor (::=)
  loc : Var a shape
  val : TypeOf a w

public export
(.update) : Heaplet shape w -> Update a shape w -> Heaplet shape w
(h :< old).update (Here ::= new) = (h :< new)
[<].update (There pos ::= v) impossible
(h :< x).update (There pos ::= v) = h.update (pos ::= v) :< x

public export
HeapletCoalg : {shape : Cell .world} -> BoxCoalg (Heaplet shape)
HeapletCoalg = MkBoxCoalg $ \w, heaplet,w',rho =>
  mapPropertyWithRelevant'
    (\a => (BoxCoalgCell a).map rho)
    heaplet

public export 0
Heap : Cell .family
Heap w = Heaplet w w

public export
Ex1 : Heap [< ConsCell, ConsCell]
Ex1 = [< [< "first of singleton", There Here]
      ,  [< "loop" , Here]
      ]

public export
extendHeap : {w : Cell .world} ->
  FamProd [< Heap , w.shift $ Heaplet w ] -|> w.shift Heap
extendHeap {w} w' [< heap , init] =
  let u = mapToProperty $ (HeapletCoalg {shape = w'}).map
           (inr {w1 = w}) heap
      v = mapToProperty init
     -- Probably terrible performance, but meh
  in propertyToMap (v ++ u)

public export
record Private (f : Cell .family) (w : Cell .world) where
  constructor Hide
  ctx : Cell .world
  val : f (ctx ++ w)


namespace Private
  public export
  pure : {0 f : Cell .family} -> f -|> Private f
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
PrivateCoal : {0 f : Cell .family} ->
  (coalg : BoxCoalg f) -> BoxCoalg (Private f)
PrivateCoal coalg = MkBoxCoalg $ \w, hidden, w', rho => Hide
  { ctx = hidden.ctx
  , val = coalg.map (Paella.Worlds.bimap id rho) hidden.val
  }

public export
-- We can hide locations
hide : {w1,w : Cell .world} -> {0 f : Cell .family} ->
  Private f (w1 ++ w) -> Private f w
hide hidden =
  Hide
    { ctx = hidden.ctx ++ w1
    , val = replace {p = f}
              (appendAssociative (hidden.ctx) w1 w)
              hidden.val
    }

public export 0
LSHandlerCarrier : (f : Cell .family) -> Cell .family
LSHandlerCarrier f = Heap -% Private f

public export
LSHandlerPsh : (coalg : BoxCoalg f) ->
  BoxCoalg $ LSHandlerCarrier f
LSHandlerPsh coalg = BoxCoalgExp

public export
val : {0 f : Cell .family} -> {coalg : BoxCoalg f} ->
  coalg =|> (LSHandlerPsh coalg)
val = coalg.curry $ \w, [< v, heap] =>
  Private.pure {f} w v

public export
-- Heap's LSAlgebra structure
LSalg : {0 f : Cell .family} -> {coalg : BoxCoalg f} ->
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
                     (BoxCoalgCell _).map rho newval)
    in eval shape [< kont shape [< rho , ()] , newHeap]
  New {a}  =>
    \roots, [< kont, newval], shape, [< rho, heap] =>
      let newheap : Heap ([< a] ++ shape)
                  := extendHeap {w = [< a]} shape
                     [< heap , [<
                        (BoxCoalgCell a).map
                          (Paella.Worlds.bimap id rho)
                       newval
                     ]]
          newloc : Var a $ [< a] ++ shape
                 := inl _ Here
          rho' : roots ~> [<a] ++ shape
          rho' = Worlds.(.) inr rho
          -- Calculate the result without hiding the new
          -- location
          result : Private f ([<a] ++ shape)
                 := kont ([< a] ++ shape)
                          [< rho' , newloc]
                          ([< a] ++ shape)
                          ([< id, newheap])
      in hide result

public export
handle :
  LSSig .Free (const $ List String) [<] ->
  Private (const (List String)) [<]
handle comp =
  let coalg = MkBoxCoalg (\w, strs, b, f => strs)
  in (LSalg {coalg}).fold (val {coalg}) [<] comp [<] [< id,[<]]
