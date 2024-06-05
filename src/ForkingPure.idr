module ForkingPure

import Paella
import Data.SnocList.Quantifiers
import Control.Monad.Writer
import Control.Monad.Identity

public export
Name : A
Name = P

public export
ValueOf : A -> Type
ValueOf P = ()

public export
ForkType : OpSig
ForkType = const () ~|> FamSum [< Var Name, const ()]

public export
WaitType : OpSig
WaitType = Var Name ~|> const ()

public export
StopType : OpSig
StopType = const () ~|> const Void

public export
PrintType : OpSig
PrintType = const String ~|> const ()

public export
data FSig : Signature where
  Fork  : FSig ForkType
  Wait  : FSig WaitType
  Stop  : FSig StopType
  Print : FSig PrintType

%hint
public export
FSigFunc : BoxCoalgSignature FSig
FSigFunc Fork = MkFunOpSig
              { Args  = BoxCoalgConst
              , Arity = BoxCoalgSum [< BoxCoalgVar, BoxCoalgConst]
              }
FSigFunc Wait = MkFunOpSig
              { Args  = BoxCoalgVar
              , Arity = BoxCoalgConst
              }
FSigFunc Stop = MkFunOpSig
              { Args  = BoxCoalgConst
              , Arity = BoxCoalgConst
              }
FSigFunc Print = MkFunOpSig
              { Args  = BoxCoalgConst
              , Arity = BoxCoalgConst
              }

export
fork : genOpType FSig ForkType
fork = genOp Fork

export
wait : genOpType FSig WaitType
wait = genOp Wait

export
stop : genOpType FSig StopType
stop = genOp Stop

export
print : genOpType FSig PrintType
print = genOp Print

parentPrint : Var Name -|> FSig .Free (const ())
parentPrint w _ = print w "parent"

childPrint : const () -|> FSig .Free (const ())
childPrint w _ = print w "child"

test : FamProd [< ] -|> FSig .Free (const ())
test =                                          (\w, [< ] =>
  fork _ ()                              ) >>== (\w, [< enu] =>
  caseSplit parentPrint childPrint _  enu)

Pure : World -> Type
Pure _ = Writer String ()

BoxCoalgPure : BoxCoalg Pure
BoxCoalgPure = MkBoxCoalg $ \w, x, w', rho => x

forkPure : FamProd [< FamSum [< Var Name, const ()] -% Pure, const ()] -|> Pure
forkPure w [< cont, ()] = do
  cont w [< id, Here ()] -- Child
  cont (w :< P) [< inl {w2 = [< P]}, There $ Here Here] -- Parent

waitPure : FamProd [< const () -% Pure, Var Name] -|> Pure
waitPure w [< cont, n] = cont w [< id, ()] -- Child is always done

stopPure : FamProd [< const Void -% Pure, const ()] -|> Pure
stopPure w [< _, ()] = tell "stopped; "

printPure : FamProd [< const () -% Pure, const String] -|> Pure
printPure w [< cont, s] = do
  tell ("[" ++ s ++ "]; ")
  cont w [< id, ()]

PureAlgebra : FSig .AlgebraOver Pure
PureAlgebra = MkAlgebraOver {sig = FSig} $ \case
  Fork => forkPure
  Wait => waitPure
  Stop => stopPure
  Print => printPure

handle : FSig .Free (const Unit) -|> Pure
handle w comp = PureAlgebra .fold (\w, () => pure ()) w comp

main : IO ()
main = putStrLn $ execWriter $ handle [< ] (test [< ] [< ])