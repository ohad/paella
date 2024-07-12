module TimeSimple

import Data.Fin
import Data.Vect

public export
infix 1 ~|>

record AlgOpSig where
  constructor (~|>)
  Args, Arity : Type

AlgSignature : Type
AlgSignature = AlgOpSig -> Type

data (.Free) : AlgSignature -> Type -> Type where
  Return : x -> sig.Free x
  Op : sig opSig -> (opSig.Args, opSig.Arity -> sig.Free x) -> sig.Free x

0 (.AlgebraOver) : AlgSignature -> Type -> Type
sig.AlgebraOver b = {0 opSig : AlgOpSig} -> 
  (op : sig opSig) -> (opSig.Arity -> b) -> (opSig.Args -> b)

(.FreeAlgOver) : (0 sig : AlgSignature) -> (0 x : Type) ->
  sig.AlgebraOver (sig.Free x)
sig.FreeAlgOver x op k args = Op op (args, k)

(.fold) : sig.AlgebraOver b -> (x -> b) -> sig.Free x -> b
alg.fold val (Return x)        = val x
alg.fold val (Op op (args, k)) = alg op (alg.fold val . k) args

0 genericOpType :
  (sig : AlgSignature) -> (opSig : AlgOpSig) -> Type
genericOpType sig opSig =
  opSig.Args -> sig.Free opSig.Arity

genericOp : (op : sig opSig) -> genericOpType sig opSig
genericOp op arg = Op op (arg, \x => Return x)

(sig : AlgSignature) => Functor sig.Free where
  map f (Return x) = Return (f x)
  map f (Op op (args, k)) = Op op (args, map f . k)

(sig : AlgSignature) => Applicative sig.Free where
  pure = Return
  (Return f) <*> x = map f x
  (Op op (args, k)) <*> x = Op op (args, \r => k r <*> x)

(sig : AlgSignature) => Monad sig.Free where
  t >>= k = (sig.FreeAlgOver b).fold k t

namespace State
  public export
  Loc : Type
  Loc = Fin 10
  
  public export
  data Bit = O | I
  
  public export
  data OpGS : AlgSignature where
    Read  : OpGS (Loc ~|> Bit)
    Write : OpGS ((Loc, Bit) ~|> Unit)
  
  export
  read : Loc -> (OpGS).Free Bit
  read = genericOp Read

  export
  write : (Loc, Bit) -> (OpGS).Free Unit
  write = genericOp Write

  public export
  Store : Type
  Store = Vect 10 Bit

  export
  InitStore : Store
  InitStore = replicate 5 O ++ replicate 5 I

  export
  DynScopeGS : (OpGS).AlgebraOver (Store -> b)
  DynScopeGS {opSig = .(Loc        ~|> Bit )} Read  k loc s =
    k (index loc s) s
  DynScopeGS {opSig = .((Loc, Bit) ~|> Unit)} Write k (loc, v) s =
    k () (replaceAt s loc v)
    where
      replaceAt : Vect n a -> Fin n -> a -> Vect n a
      replaceAt (x :: xs) FZ y = y :: xs
      replaceAt (z :: xs) (FS pos) y = z :: replaceAt xs pos y
  
  export
  Ex1 : (OpGS).Free (Bit, Bit)
  Ex1 = do
    tmp <- read 4
    write (4, !(read 5))
    write (5, tmp)
    pure (!(read 4), !(read 5))

  export
  Ex11 : (Bit, Bit)
  Ex11 = (DynScopeGS).fold (\x,s => x) Ex1 InitStore

namespace Time
  Ticky : Type
  Ticky = Int

  public export
  data OpTime : AlgSignature where
    Grab : OpTime (Unit ~|> Ticky)
    Emit : OpTime (Ticky ~|> Unit)
    Wait : OpTime (Unit ~|> Unit)
  
  export
  grab : Unit -> (OpTime).Free Ticky
  grab = genericOp Grab

  export
  emit : Ticky -> (OpTime).Free Unit
  emit = genericOp Emit

  export
  wait : Unit -> (OpTime).Free Unit
  wait = genericOp Wait

  Clocked : Type
  Clocked = Int -> IO Unit

  waiting : Clocked -> Clocked
  waiting c t = do
    putStrLn "waiting"
    getLine >>= \case
      "" => waiting c (t + 1)
      _  => c t

  ClockedTime : (OpTime).AlgebraOver Clocked
  ClockedTime {opSig = .(Unit ~|> Ticky)} Grab k x =
    \t => k t t
  ClockedTime {opSig = .(Ticky ~|> Unit)} Emit k x =
    \t => printLn (t - x) >> k () t
  ClockedTime {opSig = .(Unit ~|> Unit)}  Wait k x =
    \t => waiting (k ()) t
  
  export
  Ex1 : (OpTime).Free Unit
  Ex1 = do
    x <- grab ()
    wait ()
    y <- grab ()
    emit x
    emit y
    wait ()
    emit x
    emit y
  
  export
  Ex11 : IO ()
  Ex11 = (ClockedTime).fold (\_, _ => putStrLn "done") Ex1 0

main : IO ()
main = Time.Ex11