import Syntax.MonadicCalculus

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

record CategoryStructure obj (hom : obj -> obj -> Type) where
  constructor MkCatStruct
  comp : {a,b,c : obj} -> hom b c -> hom a b -> hom a c
  id   : (a : obj) -> hom a a

record CartesianStructure (cat : CategoryStructure obj hom) where
  constructor MkCart
  lin : obj
  snoc : obj -> obj -> obj
  hd : {a,b : obj} -> hom (snoc a b) a
  tl : {a,b : obj} -> hom (snoc a b) b
  tuple : {a,b,c : obj} -> hom c a -> hom c b -> hom c (a `snoc` b)

record MonadStructure (cat : CategoryStructure obj hom)
                      (cart : CartesianStructure cat) where
  constructor MkMonad
  func : obj -> obj
  pure : {o : obj} -> hom o (func o)
  bind : {g,a,b : obj} -> hom (cart.snoc g a) (func b) ->
                          hom (cart.snoc g (func a)) (func b)

record NameMe obj hom where
  constructor MkMe
  cat : CategoryStructure obj hom
  car : CartesianStructure cat
  mon : MonadStructure cat car

0
SemBase : NameMe obj hom -> Type -> Type
SemBase {hom,obj} cat ty = ty -> obj

semCtx : (cat : NameMe obj hom) ->
  (semBase : SemBase cat (Ty base)) ->
  (ctx : Context (Ty base)) -> obj
semCtx cat semBase [<] = cat.car.lin
semCtx cat semBase (sx :< (x, ty)) = cat.car.snoc (semCtx cat semBase sx) (semBase ty)

--interp : NameMe obj hom -> Term MemMan ctx ty -> ?h890
