module LocalState

import Paella

public export
ConsCell : A
ConsCell = P

public export
-- Postulate: each parameter has a type
-- For now, just cons cells
TypeOf : A -> Family
TypeOf P =
  (FamProd [< const String, Var ConsCell])

public export
TypeOfFunctoriality : (a : A) -> PresheafOver $ TypeOf a
-- Should propagate structure more nicely
TypeOfFunctoriality P rho ([< str , loc]) =
  [< str , rho _ loc]

%hint
public export
TypeOfBoxFunctoriality : (a : A) -> BoxCoalg $ TypeOf a
-- Should propagate structure more nicely
TypeOfBoxFunctoriality a = cast {from = PresheafOver _} (TypeOfFunctoriality a)



public export
||| Type of reading an A-cell
readType : A -> OpSig
readType a = MkOpSig
  { Args = Var a
  , Arity = TypeOf a
  }

public export
||| Type of writing an a
||| w_0 : [a, []]
writeType : A -> OpSig
writeType a = MkOpSig
  { Args = FamProd [< Var a, TypeOf a]
  , Arity = const ()
  }


public export
||| Allocate a fresh cell storing an a value
newType : A -> OpSig
newType a = MkOpSig
  { Args = [< a].shift (TypeOf a)
  , Arity = Var a
  }

public export
LSSig : Signature
LSSig = [
  readType ConsCell,
  writeType ConsCell,
  newType ConsCell
]

%hint
public export
LSSigFunc : FunctorialSignature LSSig
LSSigFunc =
  [ -- read
    MkFunOpSig { Arity = BoxCoalgProd [< BoxCoalgConst, BoxCoalgVar]
               , Args = BoxCoalgVar
               }
  , -- write
    MkFunOpSig { Arity = BoxCoalgConst
               , Args = (BoxCoalgProd [< BoxCoalgVar,
                                         cast {from = PresheafOver (TypeOf ConsCell)}
                                         (TypeOfFunctoriality ConsCell)])
               }
  , -- new
    MkFunOpSig { Arity = BoxCoalgVar
               , Args = ([< ConsCell].shiftCoalg {f = (TypeOf ConsCell)} $
                     cast {from = PresheafOver (TypeOf ConsCell)}
                     (TypeOfFunctoriality ConsCell))
               }
  ]

-- Probably better to define the generic operations generically
-- and instantiate to these

-- Can derive from previous but can cut out hassle
public export
abst :
  (f -|> g) ->
  (f -% g).elem
abst f w w' [< rho , x] = f w' x

public export
read : Var ConsCell -|> LSSig .Free (TypeOf ConsCell)
read w loc =
  Op (LSSig ?! 0) w
     [< loc , abst pure w]

public export
write : FamProd [< Var ConsCell , TypeOf ConsCell] -|>
          LSSig .Free (const ())
write w locval =
  Op (LSSig ?! 1) w
     [< locval , abst pure w]


public export
new : FamProd [< [<ConsCell].shiftLeft (TypeOf ConsCell)] -|>
      LSSig .Free (Var ConsCell)
new w [<val] =
  -- move new location to the bottom of the heap
  let val' = (TypeOfFunctoriality ConsCell)
        (swapRen {w1 = w, w2 = [<ConsCell]}) val
  in Op (LSSig ?! 2) w
    [< val' , abst pure w]

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
    (\a => TypeOfFunctoriality a rho)
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
  , val = coalg.map (Paella.bimap idRen rho) hidden.val
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
LSalg = MkAlgebraOver
  [ -- readType
     \roots, [< kont, loc], shape, [< rho, heap] =>
       let result = heap !! (rho _ loc)
       in eval shape [< kont shape [< rho , result] , heap]
  , -- writeType
    \roots, [< kont, [<loc, newval]], shape, [< rho, heap] =>
       let newHeap = heap.update
                     (rho _ loc ::=
                        TypeOfFunctoriality ConsCell rho newval)
       in eval shape [< kont shape [< rho , ()] , newHeap]
  , -- new
    \roots, [< kont, newval], shape, [< rho, heap] =>
      let newheap : Heap ([< ConsCell] ++ shape)
                  := extendHeap {w = [< ConsCell]} shape
                     [< heap , [<
                       TypeOfFunctoriality ConsCell
                         (Paella.bimap idRen rho)
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
                          ([< idRen, newheap])
      in hide result
  ]

public export
handle :
  LSSig .Free (const $ List String) [<] ->
  Private (const (List String)) [<]
handle comp =
  let coalg = MkBoxCoalg (\w, strs, b, f => strs)
  in (LSalg {coalg}).fold (val {coalg}) [<] comp [<] [< idRen,[<]]