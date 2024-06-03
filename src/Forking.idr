module Forking

import Paella
import Control.Monad.Maybe
import Control.Monad.Error.Interface

public export
Name : A
Name = P

public export
ValueOf : A -> Type
ValueOf P = ThreadID

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

ignorePrint : Var Name -|> FSig .Free (const ())
ignorePrint w _ = print w "Parent"

constAbsurd : const Void -|> const ()
constAbsurd _ x = ()

stopUnit : const () -|> FSig .Free (const ())
stopUnit = BoxCoalgConst .fmap constAbsurd . stop

axiom2 : FamProd [< ] -|> FSig .Free (const ())
axiom2 =                                      (\w, [< ] =>
  fork _ ()                            ) >>== (\w, [< enu] =>
  caseSplit ignorePrint stopUnit _ enu )

splitExp : (FamSum [< f1, f2] -% g) -|> FamProd [< f1 -% g, f2 -% g]
splitExp w h =
  [< \w', [< rho, f1] => h w' [< rho, There (Here f1)]
  ,  \w', [< rho, f2] => h w' [< rho, Here f2]
  ]

export
TIDs : Family
TIDs w = ForAll w ValueOf

toFunc : {w : World} -> TIDs w -> ((a : A) -> Var a w -> ValueOf a)
toFunc [<] _ _ impossible
toFunc (tid :< tids) _ Here = tids
toFunc (tid :< tids) _ (There pos) = toFunc tid _ pos

fromFunc : {w : World} -> ((a : A) -> Var a w -> ValueOf a) -> TIDs w
fromFunc {w = [<]} f = [<]
fromFunc {w = (sx :< x)} f =
  fromFunc {w = sx} (\_, pos => f _ (There pos)) :< f _ Here

mapTIDs : {w, w' : World} -> (w ~> w') -> TIDs w' -> TIDs w
mapTIDs rho tids = fromFunc (\a => toFunc tids a . rho a)

export
MIO : Family
MIO w = TIDs w -> MaybeT IO ()

%hint
export
BoxCoalgMIO : BoxCoalg MIO
BoxCoalgMIO = MkBoxCoalg $ \w, mio, w', rho => mio . mapTIDs rho

forkMIO : FamProd [< FamSum [< Var Name, const ()] -% MIO, const ()] -|> MIO
forkMIO w [< cont, ()] =
  let [< parent, child] = splitExp w cont in
  ?res

waitMIO : FamProd [< const () -% MIO, Var Name] -|> MIO

stopMIO : FamProd [< const Void -% MIO, const ()] -|> MIO
stopMIO w [< _, ()] _ = throwError ()

printMIO : FamProd [< const () -% MIO, const String] -|> MIO
printMIO w [< cont, s] tids = do
  print s
  cont w [< id, ()] tids

MIOAlgebra : FSig .AlgebraOver MIO
MIOAlgebra = MkAlgebraOver {sig = FSig} $ \case
  Fork => forkMIO
  Wait => waitMIO
  Stop => stopMIO
  Print => printMIO