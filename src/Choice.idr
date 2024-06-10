module Choice

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
ChooseType : OpSig
ChooseType = const () ~|> FamSum [< const (), const ()]

public export
PrintType : OpSig
PrintType = const String ~|> const ()

public export
data CSig : Signature where
  Choose : CSig ChooseType
  Print  : CSig PrintType

%hint
public export
CSigFunc : BoxCoalgSignature CSig
CSigFunc Choose = MkFunOpSig
  { Args  = BoxCoalgConst
  , Arity = BoxCoalgSum [< BoxCoalgConst, BoxCoalgConst]
  }
CSigFunc Print = MkFunOpSig
  { Args  = BoxCoalgConst
  , Arity = BoxCoalgConst
  }

export
choose : genOpType CSig ChooseType
choose = genOp Choose

export
print : genOpType CSig PrintType
print = genOp Print

ignorePrint : String -> (const () -|> CSig .Free (const ()))
ignorePrint s w  _ = print w s

test : FamProd [< ] -|> CSig .Free (const ())
test =               (\w, [< ] =>
  choose _ () ) >>== (\w, [< coc] =>
  caseSplit (ignorePrint "left") (ignorePrint "right") _ coc )

Pure : World -> Type
Pure _ = Writer String ()

BoxCoalgPure : BoxCoalg Pure
BoxCoalgPure = MkBoxCoalg $ \w, x, w', rho => x

choosePure : FamProd [< FamSum [< const (), const ()] -% Pure, const ()] -|> Pure
choosePure w [< cont, ()] = do
  cont w [< id, Here ()]
  cont w [< id, There (Here ())]

printPure : FamProd [< const () -% Pure, const String] -|> Pure
printPure w [< cont, s] = do
  tell ("[" ++ s ++ "]; ")
  cont w [< id, ()]

PureAlgebra : CSig .AlgebraOver Pure
PureAlgebra = MkAlgebraOver {sig = CSig} $ \case
  Choose => choosePure
  Print => printPure

handle : CSig .Free (const Unit) -|> Pure
handle w comp = PureAlgebra .fold (\w, () => pure ()) w comp

main : IO ()
main = putStrLn $ execWriter $ handle [< ] (test [< ] [< ])