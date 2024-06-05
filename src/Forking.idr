module Forking

import Paella
import Control.Monad.Trans
import Control.Monad.Maybe
import Control.Monad.Error.Interface
import Data.IORef
import Data.SnocList.Quantifiers
import Debug.Trace

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
ignorePrint w _ = print w "parent"

constAbsurd : const Void -|> const ()
constAbsurd _ x = ()

stopPrint : const () -|> FSig .Free (const Void)
stopPrint w () = BoxCoalgConst .extend stop w . print w $ "stopping"

stopUnit : const () -|> FSig .Free (const ())
stopUnit = BoxCoalgConst .fmap constAbsurd . stopPrint

axiom2 : FamProd [< ] -|> FSig .Free (const ())
axiom2 =                                      (\w, [< ] =>
  fork _ ()                            ) >>== (\w, [< enu] =>
  print _ "splitting"                  ) >>== (\w, [< enu, ()] =>
  caseSplit ignorePrint stopUnit _ enu ) >>== (\w, [< enu, (), ()] =>
  print _ "done"                       )

parentPrint : Var Name -|> FSig .Free (const ())
parentPrint w _ = print w "parent"

childPrint : const () -|> FSig .Free (const ())
childPrint w _ = print w "child"

viewing : FamSum [< Var P, const ()] w -> String
viewing (Here x) = "DEBUG: unit"
viewing (There (Here x)) = "DEBUG: var"

test : FamProd [< Var Name] -|> FSig .Free (const ())
test =                                          (\w, [< n] =>
  fork _ ()                              ) >>== (\w, [< n, enu] =>
  caseSplit parentPrint childPrint _  (traceValBy viewing enu))

splitExp : (FamSum [< f1, f2] -% g) -|> FamProd [< f1 -% g, f2 -% g]
splitExp w h =
  [< \w', [< rho, f1] => h w' [< rho, There (Here f1)]
  ,  \w', [< rho, f2] => h w' [< rho, Here f2]
  ]

export
TIDs : Family
TIDs w = ForAll w (\a => (ValueOf a, IORef Bool))

toFunc : {w : World} ->
  TIDs w -> ((a : A) -> Var a w -> (ValueOf a, IORef Bool))
toFunc [<] _ _ impossible
toFunc (tid :< tids) _ Here = tids
toFunc (tid :< tids) _ (There pos) = toFunc tid _ pos

fromFunc : {w : World} ->
  ((a : A) -> Var a w -> (ValueOf a, IORef Bool)) -> TIDs w
fromFunc {w = [<]} f = [<]
fromFunc {w = (sx :< x)} f =
  fromFunc {w = sx} (\_, pos => f _ (There pos)) :< f _ Here

mapTIDs : {w, w' : World} -> (w ~> w') -> TIDs w' -> TIDs w
mapTIDs rho tids = fromFunc (\a => toFunc tids a . rho a)

getTID : {w : World} -> Var a w -> TIDs w -> (ValueOf a, IORef Bool)
getTID Here (_ :< tid) = tid
getTID (There pos) (tids :< tid) = getTID pos tids

export
MIO : Family
MIO w = TIDs w -> MaybeT IO ()

%hint
export
BoxCoalgMIO : BoxCoalg MIO
BoxCoalgMIO = MkBoxCoalg $ \w, mio, w', rho => \tids => do
  putStrLn {io = MaybeT IO} "ACTION"
  (mio . mapTIDs rho) tids

forkMIO : FamProd [< FamSum [< Var Name, const ()] -% MIO, const ()] -|> MIO
forkMIO w [< cont', ()] =
  \tids => MkMaybeT $ do
    inst <- newIORef 0
    let cont = \w, x, tids => do
      modifyIORef inst (+ 1)
      i <- readIORef inst
      putStrLn ("INST: " ++ show i)
      trace "-- cont" $ cont' w x tids
    putStrLn "== Fork =="
    -- See if child errors out
    putStrLn "> Starting fork"
    errored <- newIORef False
    putStrLn "> Made IO ref"
    let childM = runMaybeT $ do
      putStrLn "> child: starting body"
      -- Catch the childs error and write to the IO ref
      catchError (do
          cont w [< id, traceValBy viewing $ Here ()] tids
          putStrLn "> child: finished body"
        ) $ \_ => do
          putStrLn "> child: errored"
          writeIORef errored True
    -- Fork the adapted child
    putStrLn "> Forking child"
    tid <- Prelude.IO.fork (map (\x => ()) $ childM)
    -- Run the parent in the extended world
    putStrLn "> Starting parent"
    runMaybeT $ do
      putStrLn {io = MaybeT IO} "> parent: starting body"
      cont (w :< P) [< inl {w2 = [< P]}, traceValBy viewing $ There $ Here Here] (tids :< (tid, errored))
      putStrLn "> parent: finished body"

waitMIO : FamProd [< const () -% MIO, Var Name] -|> MIO
waitMIO w [< cont, n] = \tids => do
  let (tid, stopped) = getTID n tids
  lift $ threadWait tid
  s <- readIORef stopped
  if s then cont w [< id, ()] tids else putStrLn "> Didn't call stop"

stopMIO : FamProd [< const Void -% MIO, const ()] -|> MIO
stopMIO w [< _, ()] _ = throwError ()

printMIO : FamProd [< const () -% MIO, const String] -|> MIO
printMIO w [< cont, s] tids = do
  putStrLn "== Print =="
  putStrLn s
  cont w [< id, ()] tids

MIOAlgebra : FSig .AlgebraOver MIO
MIOAlgebra = MkAlgebraOver {sig = FSig} $ \case
  Fork => forkMIO
  Wait => waitMIO
  Stop => stopMIO
  Print => printMIO

handle : FSig .Free (const Unit) -|> MIO
handle w comp = MIOAlgebra .fold (\w, (), tids => pure ()) w comp

-- main : IO (Maybe Unit)
-- main = do
--   iob <- newIORef True
--   tid <- fork (pure ())
--   runMaybeT $ handle [< P] (test [< P] [< Here]) [< (tid, iob)]

sanity : IO (Maybe Unit)
sanity =
  let [< parent, child] = splitExp [< ] $
    abst (caseSplit parentPrint childPrint) [< ]
  in
  do
    iob <- newIORef True
    tid <- fork $ do
      _ <- runMaybeT $ handle [< ] (child [< ] [< id, ()]) [< ]
      pure ()
    runMaybeT $ handle [< P] (parent [< P] [< inl {w2 = [< P]}, Here]) [< (tid, iob)]

example : Either ThreadID () -> IO ()
example (Left tid) = putStrLn "parent"
example (Right ()) = putStrLn "child"

split : (Either a b -> c) -> (a -> c, b -> c)
split f = (\x => f (Left x), \x => f (Right x))

-- main : IO ()
-- main = do
--   let (parent, child) = split example
--   tid <- fork (child ())
--   parent tid

main : IO (Maybe Unit)
main = runMaybeT $ do
  let cont = \b => print {io = MaybeT IO} b
  cont True
  cont False