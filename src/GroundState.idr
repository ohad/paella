module GroundState

import Paella

toRen : Var P w -> ((Node Leaf (Just P) Leaf) ~> w)
toRen []      P []     = []
toRen []      _ (L []) impossible
toRen []      _ (R []) impossible
toRen (L pos) a v'     = L (toRen pos a v')
toRen (R pos) a v'     = R (toRen pos a v')

public export
data Free : World -> Type where
  Nil : Free $ Node l Nothing r
  L : Free l -> Free $ Node l d r
  R : Free r -> Free $ Node l d r

Status : World -> Maybe A -> Type
Status w Nothing = Free w
Status w (Just a) = Var a w

statusL : {mx : Maybe A} -> Status l mx -> Status (Node l d r) mx
statusL {mx = Nothing} s = L s
statusL {mx = (Just x)} s = L s

statusR : {mx : Maybe A} -> Status r mx -> Status (Node l d r) mx
statusR {mx = Nothing} s = R s
statusR {mx = (Just x)} s = R s

residency : (w : World) -> ForAllM w (Status w)
residency Leaf = Leaf
residency (Node l Nothing r) =
  let l' = mapPropertyWithRelevant statusL (residency l)
      r' = mapPropertyWithRelevant statusR (residency r)
  in Node l' Nil r'
residency (Node l (Just x) r) =
  let l' = mapPropertyWithRelevant statusL (residency l)
      r' = mapPropertyWithRelevant statusR (residency r)
  in Node l' Nil r'

||| Extend a world with a single new variable
||| How do you enforce more about this?
public export
record Extension (a : A) (w : World) where
  constructor Extend
  w' : World
  rho : w ~> w'
  var : Var a w'

||| Extend a world by filling in a free spot
extend : {a : A} -> (w : World) -> Free w -> Extension a w
extend (Node l Nothing r) Nil =
  Extend (Node l (Just a) r) (cotuple winl winr) Nil
extend (Node l d r) (L pos) =
  let lext = extend {a} l pos
      rho' = bimap {w1 = l, w1' = lext.w'} lext.rho id
  in Extend (Node (lext.w') d r) rho' (L lext.var)
extend (Node l d r) (R pos) =
  let rext = extend {a} r pos
      rho' = bimap {w2 = r, w2' = rext.w'} id rext.rho
  in Extend (Node l d (rext.w')) rho' (R rext.var)

extendVar : {a : A} -> {w : World} ->
  Var a w -> (ext : Extension b w) -> Var a ext.w'
extendVar v ext = ext.rho _ v

Eq (Var a w) where
  Nil   == Nil   = True
  (L x) == (L y) = x == y
  (R x) == (R y) = x == y
  _     == _     = False

Single : A -> World
Single x = Node Leaf (Just x) Leaf

splitAll : {tx, ty : Tree _} ->
  All p (tx ++ ty) -> (All p tx, All p ty)
splitAll (Node l () r) = (l, r)

joinAll : {tx, ty : Tree _} ->
  All p tx -> All p ty -> All p (tx ++ ty)
joinAll ta tb = Node ta () tb

splitAllM : {tx, ty : Tree _} ->
  AllM p (tx ++ ty) -> (AllM p tx, p Nothing, AllM p ty)
splitAllM (Node l x r) = (l, x, r)

joinAllM : {tx, ty : Tree _} ->
  AllM p tx -> p Nothing -> AllM p ty -> AllM p (tx ++ ty)
joinAllM ta mx tb = Node ta mx tb

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
readType a = MkOpSig
  { Args = Var a
  , Arity = TypeOf a
  }

||| Type of writing an A-cell
writeType : A -> OpSig
writeType a = MkOpSig
  { Args = FamProd [< Var a, TypeOf a]
  , Arity = const ()
  }

||| Allocate a fresh cell storing an a value
public export
newType : A -> OpSig
newType a = MkOpSig
  { Args = TypeOf a
  , Arity = Var a
  }

||| Type of equality testing:
public export
equalType : A -> OpSig
equalType a = MkOpSig
  { Args = FamProd [< Var a, Var a]
  , Arity = const Bool
  }

public export
LSSig : Signature
LSSig = [
  readType IntCell,
  writeType IntCell,
  newType IntCell,
  equalType IntCell
]

%hint
public export
LSSigFunc : BoxCoalgSignature LSSig
LSSigFunc =
  [ -- read
    MkFunOpSig { Arity = BoxCoalgA IntCell
               , Args = BoxCoalgVar
               }
  , -- write
    MkFunOpSig { Arity = BoxCoalgConst
               , Args = BoxCoalgProd [< BoxCoalgVar, BoxCoalgA IntCell]
               }
  , -- new
    MkFunOpSig { Arity = BoxCoalgVar
               , Args = BoxCoalgA IntCell
               }
  , -- equal
    MkFunOpSig { Arity = BoxCoalgConst
               , Args = BoxCoalgProd [< BoxCoalgVar, BoxCoalgVar]
               }
  ]


-- Probably better to define the generic operations generically
-- and instantiate to these

-- Can derive from previous but can cut out hassle
abst : (f -|> g) -> (f -% g).elem
abst alpha w' w'' [< rho, x] = alpha w'' x

unabst : (f -% g).elem -> (f -|> g)
unabst alpha w' x = alpha w' w' [< id, x]

export
read : Var IntCell -|> LSSig .Free (TypeOf IntCell)
read w loc = Op (LSSig ?! 0) w [< loc, abst pure w]

export
write : FamProd [< Var IntCell, TypeOf IntCell] -|> LSSig .Free (const ())
write w locval = Op (LSSig ?! 1) w [< locval, abst pure w]

export
new : (Single IntCell).shiftLeft (TypeOf IntCell) -|> LSSig .Free (Var IntCell)
new w val =
  -- move new location to the bottom of the heap
  let val' = (BoxCoalgA IntCell).map (swapRen {l = w, r = Single IntCell}) val
  in Op (LSSig ?! 2) w [< val', abst pure w]

equal : FamProd [< Var IntCell, Var IntCell] -|> LSSig .Free (const Bool)
equal w vpair = Op (LSSig ?! 3) w [< vpair, abst pure w]

StateIn : Family
StateIn w = ForAllM w (MaybeP ValueOf)

getComponent : Var a w -> StateIn w -> ValueOf a
getComponent []      (Node _ x _) = x
getComponent (L pos) (Node l _ _) = getComponent pos l
getComponent (R pos) (Node _ _ r) = getComponent pos r

setComponent : Var a w -> StateIn w -> ValueOf a -> StateIn w
setComponent []      (Node l _ r) y = Node l y r
setComponent (L pos) (Node l x r) y = Node (setComponent pos l y) x r
setComponent (R pos) (Node l x r) y = Node l x (setComponent pos r y)

allocComponent : {a : A} ->
  (w : World) -> Free w -> StateIn w -> ValueOf a ->
  (ext : Extension a w ** StateIn ext.w')
allocComponent (Node l Nothing r) [] (Node sl () sr) v =
  (Extend (Node l (Just a) r) (cotuple winl winr) Nil ** Node sl v sr)
allocComponent (Node l d r) (L pos) (Node sl ms sr) v =
  case (allocComponent l pos sl v) of
    (Extend l' rhol varl ** sl') =>
      (Extend (Node l' d r) (bimap rhol id) (L varl) ** Node sl' ms sr)
allocComponent (Node l d r) (R pos) (Node sl ms sr) v =
  case (allocComponent r pos sr v) of
    (Extend r' rhor varr ** sr') =>
      (Extend (Node l d r') (bimap id rhor) (R varr) ** Node sl ms sr')

-- Viewed as in Inj-presheaf, free Inj-LS algebra on the presheaf which is
-- constantly t
Heap : Type -> Family
Heap t w = (Maybe (Free w), StateIn w) -> Pair t (StateIn w)

{-
pureHeap : {w : World} -> t -> Heap t w
pureHeap t = \x => (t, HideStateIn w id x [])

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
-}
newHeapOp :
  FamProd [< Env (Single IntCell) -% Heap t, TypeOf IntCell] -|> Heap t
newHeapOp q [< cont, val] (Nothing, ss) =
  let combined = joinAllM (Node {mx = Just IntCell} Leaf val Leaf) () ss
      (t, ss') = cont
        (Node (Node Leaf (Just P) Leaf) Nothing q)
        [< inr, inl]
        (Just Nil, combined)
  in (t, snd . snd $ splitAllM ss')
newHeapOp q [< cont, val] (Just f, ss) =
  case (allocComponent {a = IntCell} q f ss val) of
    (Extend w' rho var ** ss') =>
      let shed = cont w' [< rho, toRen var] (Nothing, ss')
      in ?res

  -- let combined = joinAll (Node Leaf val Leaf) ss
  --     (t, ss') = cont combined
  -- in (t, snd (splitAll ss'))
{-
-- The action of the injection n -> n + 1 of Inj on the heap
extendHeap : Heap t -|> (Single IntCell).shift (Heap t)
extendHeap w h sv =
  let (v', sv') = splitAll sv
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
  let rho' = bimap id rho
      cont' = cont
        (Single P ++ w)
        [< inr, swapRen P (R Nil)]
        (Single P ++ w')
        rho'
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
LocHeapAlgebra = MkAlgebraOver [
  readLocHeapOp,
  writeLocHeapOp,
  newLocHeapOp,
  equalLocHeapOp
]

-- The unit of the local state monad gave pureHeap, this is the right Kan
-- extension of Inj -> Fin applied to it. Thus, this is the needed algebra.
pureLocHeap : t -> LocHeap t w
pureLocHeap t w rho = pureHeap t

-- l1 := !l2
readWrite : FamProd [< Var IntCell, Var IntCell] -|> LSSig .Free (const Unit)
readWrite =
                             (\w, [< l1, l2]      =>
  read _ l2           ) >>== (\w, [< l1, l2, val] =>
  write _ [< l1, val] )

-- swap value of two locations with temp location
swap : FamProd [< Var IntCell, Var IntCell] -|> LSSig .Free (const Unit)
swap =
                                (\w, [< l1, l2]             =>
  new _ 0                ) >>== (\w, [< l1, l2, lt]         =>
  readWrite _ [< lt, l1] ) >>== (\w, [< l1, l2, lt, ()]     =>
  readWrite _ [< l1, l2] ) >>== (\w, [< l1, l2, lt, (), ()] =>
  readWrite _ [< l2, lt] )

handle : LSSig .Free (const Unit) -|> LocHeap Unit
handle w comp = LocHeapAlgebra .fold (\w, _ => pureLocHeap ()) w comp

TwoIntCell : World
TwoIntCell = (Single IntCell ++ Single IntCell)

Ex : (Unit, StateIn TwoIntCell)
Ex = handle TwoIntCell (
    GroundState.swap TwoIntCell [< L Nil, R Nil]
  ) TwoIntCell id (Node (Node Leaf 1 Leaf) () (Node Leaf 2 Leaf))
-}