import Syntax.MonadicCalculus
import Data.SnocList.Quantifiers

import Paella
import LocalState

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
  comp : {0 a,b,c : obj} -> hom b c -> hom a b -> hom a c
  id   : (0 a : obj) -> hom a a

record (.Presheaf) (sig : Type) where
  constructor With
  0 family : sig.family
  action : BoxCoalg family

public export
infix 1 ~|>

0
(~|>) : (src, tgt : sig.Presheaf) -> Type
src ~|> tgt = src.family -|> tgt.family

-- -- TODO:
PshCat : CategoryStructure (sig.Presheaf) (~|>)
PshCat = MkCatStruct
  { comp = (.)
  , id = \f => Families.id
  }

record CartesianStructure (cat : CategoryStructure obj hom) where
  constructor MkCart
  unit : obj
  bang : {0 a : obj} -> hom a unit
  prod : obj -> obj -> obj
  fst : {0 a,b : obj} -> hom (prod a b) a
  snd : {0 a,b : obj} -> hom (prod a b) b
  tuple : {0 a,b,c : obj} -> hom c a -> hom c b -> hom c (a `prod` b)

PshCart : CartesianStructure (PshCat {sig})
PshCart = MkCart
  { unit  =  FamProd [<] `With` ?h891
  , bang  = \w, x => [<]
  , prod  = \x,y => FamProd [< x.family,y.family] `With` BoxCoalgProd [< x.action, y.action]
  , fst   = \w, [< x, y] => x
  , snd   = \w, [< x, y] => y
  , tuple = \f, g, w, u => [< f w u , g w u]
  }

record MonadStructure (cat : CategoryStructure obj hom)
                      (cart : CartesianStructure cat) where
  constructor MkMonad
  func : obj -> obj
  pure : {o : obj} -> hom o (func o)
  bind : (g,a,b : obj) -> hom (cart.prod g a) (func b) ->
         hom (cart.prod g (func a)) (func b)

-- -- TODO
FreeMonad : (signa : sig.signature) ->
  BoxCoalgSignature signa ->
  MonadStructure (PshCat {sig}) (PshCart {sig})
FreeMonad signa sigbox = MkMonad
  { func = \f => signa.Free f.family `With` BoxCoalgFree sigbox f.action
  , pure = Return
  , bind = \gamma,f,g,k =>
         let 0 p = (>>==) {f=f.family,g=g.family,sigCoalg = sigbox, gammas= ?h1889, gammaCoalgs = ?h189, fCoalg = f.action, gCoalg = g.action} ?h89
         in ?h71
  }


record ModelStructure obj hom where
  constructor MkModel
  cat : CategoryStructure obj hom
  car : CartesianStructure cat
  mon : MonadStructure cat car

0
SemBase : ModelStructure obj hom -> Type -> Type
SemBase {hom,obj} cat base = (ty : base) -> obj

0
semType : (cat : ModelStructure obj hom) ->
          (semBase : SemBase cat base) -> Ty base -> obj
semType cat semBase (Base a) = semBase a
semType cat semBase Unit = cat.car.unit
semType cat semBase (Pair a b) = cat.car.prod (semType cat semBase a)
                                              (semType cat semBase b)
semType cat semBase (T a) = cat.mon.func (semType cat semBase a)

0
semCtx : (cat : ModelStructure obj hom) ->
  (semBase : SemBase cat base) ->
  (ctx : Context (Ty base)) -> obj
semCtx cat semBase [<] = cat.car.unit
semCtx cat semBase (sx :< (x, ty))
  = cat.car.prod (semCtx cat semBase sx) (semType cat semBase ty)

0
SemEnv : (cat : ModelStructure obj hom) -> SemBase cat base ->
  Syntax base -> Type
SemEnv {hom,obj} cat semBase syn = Env syn.primitives
  (\prim => hom (semType cat semBase prim.arg)
                (semType cat semBase prim.result))

interpVar : {0 ctx : Context (Ty base)} -> {0 type : Ty base} ->
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
         {0 ty : Ty base} ->
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
interp cat semBase semEnv (Fst t) =
  let f = interp cat semBase semEnv t
  in cat.cat.comp cat.car.fst f
interp cat semBase semEnv (Snd t) =
  let f = interp cat semBase semEnv t
  in cat.cat.comp cat.car.snd f
interp cat semBase semEnv (PrimApp p t) =
  let argSem = interp cat semBase semEnv t
      primSem = get semEnv (forgetName p)
  in cat.cat.comp primSem argSem
interp cat semBase semEnv (Let x t1 t2) = ?interp_rhs_6
interp cat semBase semEnv (Pure t) = ?interp_rhs_7
interp cat semBase semEnv (Bind x t1 t2) = ?interp_rhs_8
