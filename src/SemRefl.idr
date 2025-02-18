import Syntax.MonadicCalculus
import Data.SnocList.Quantifiers

data BaseType = Loc | Bit

MemMan : Syntax BaseType
MemMan = `[
    read : Loc -> T Bit
    write : Loc -> Bit -> T ()
    alloc : Bit -> T Loc
    true : Bit
    false : Bit
  ]

t : Term MemMan [<] `(T (Bit, Bit))
t = `(do
    a <- alloc false
    b <- alloc false
    write (a, true)
    x <- read a
    y <- read b
    pure (x, y)
  )

ForAll : (xs : SnocList a) -> (p : a -> Type) -> Type
ForAll xs p = All p xs

record CategoryStructure obj (hom : obj -> obj -> Type) where
  constructor MkCatStruct
  comp : {a,b,c : obj} -> hom b c -> hom a b -> hom a c
  id   : (a : obj) -> hom a a

-- -- TODO:
-- PshCat : CategoryStructure  (sig.Family) (-|>)

record CartesianStructure (cat : CategoryStructure obj hom) where
  constructor MkCart
  unit : obj
  bang : {a : obj} -> hom a unit
  prod : obj -> obj -> obj
  fst : {a,b : obj} -> hom (prod a b) a
  snd : {a,b : obj} -> hom (prod a b) b
  tuple : {a,b,c : obj} -> hom c a -> hom c b -> hom c (a `prod` b)

-- -- TODO
-- PshCart : CartesianStructure PshCat

record MonadStructure (cat : CategoryStructure obj hom)
                      (cart : CartesianStructure cat) where
  constructor MkMonad
  func : obj -> obj
  pure : {o : obj} -> hom o (func o)
  bind : {g,a,b : obj} -> hom (cart.prod g a) (func b) ->
         hom (cart.prod g (func a)) (func b)

-- -- TODO
-- FreeMonad : MonadStructure PshCat PshCart

record ModelStructure obj hom where
  constructor MkModel
  cat : CategoryStructure obj hom
  car : CartesianStructure cat
  mon : MonadStructure cat car

0
SemBase : ModelStructure obj hom -> Type -> Type
SemBase {hom,obj} cat base = (ty : base) -> obj

semType : (cat : ModelStructure obj hom) ->
          (semBase : SemBase cat base) -> Ty base -> obj
semType cat semBase (Base a) = semBase a
semType cat semBase Unit = cat.car.unit
semType cat semBase (Pair a b) = cat.car.prod (semType cat semBase a)
                                              (semType cat semBase b)
semType cat semBase (T a) = cat.mon.func (semType cat semBase a)

semCtx : (cat : ModelStructure obj hom) ->
  (semBase : SemBase cat base) ->
  (ctx : Context (Ty base)) -> obj
semCtx cat semBase [<] = cat.car.unit
semCtx cat semBase (sx :< (x, ty))
  = cat.car.prod (semCtx cat semBase sx) (semType cat semBase ty)

0
SemEnv : (cat : ModelStructure obj hom) -> SemBase cat base ->
  Syntax base -> Type
SemEnv {hom,obj} cat semBase syn = ForAll syn.primitives
  (\(_,prim) => hom (semType cat semBase prim.arg)
                    (semType cat semBase prim.result))

interpVar : {ctx : Context (Ty base)} -> {type : Ty base} ->
   (cat : ModelStructure obj hom) ->
   (semBase : SemBase cat base) ->
   Var ctx type ->
   hom (semCtx cat semBase ctx)
       (semType cat semBase type)
interpVar {ctx = ctx' :< (_, type)}
   cat semBase Here = cat.car.snd
interpVar {ctx = ctx' :< (y, type')}
  cat semBase (There var) =
  let var' : hom (semCtx _ _ ctx') (semType _ _ type)
           = interpVar cat semBase var
  in cat.cat.comp var' cat.car.fst

interp : (cat : ModelStructure obj hom) ->
         (semBase : SemBase cat base) ->
         (semEnv  : SemEnv cat semBase syn) ->
         {ty : Ty base} ->
         {ctx : Context (Ty base)} ->
         Term syn ctx ty ->
         hom (semCtx cat semBase ctx)
             (semType cat semBase ty)
interp cat semBase semEnv (Var var) = interpVar cat semBase var
interp cat semBase semEnv MkUnit = cat.car.bang
interp cat semBase semEnv (MkPair t1 t2) = 
  let f1 = interp cat semBase semEnv t1
      f2 = interp cat semBase semEnv t2 
  in cat.car.tuple f1 f2
interp cat semBase semEnv (Fst x) = ?interp_rhs_3
interp cat semBase semEnv (Snd x) = ?interp_rhs_4
interp cat semBase semEnv (PrimApp x y) = ?interp_rhs_5
interp cat semBase semEnv (Let nm x y) = ?interp_rhs_6
interp cat semBase semEnv (Pure x) = ?interp_rhs_7
interp cat semBase semEnv (Bind nm x y) = ?interp_rhs_8
