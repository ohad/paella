module Time

import Paella

data Ticky : World -> Type where
  Clock : Int -> Ticky t

%hint
BoxCoalgTicky : BoxCoalg Ticky
BoxCoalgTicky = MkBoxCoalg $ \t1, x, t2, le =>
  case le of
    Now => x
    Later le' =>
      case (BoxCoalgTicky .map le' x) of
        Clock i => Clock (i + 1)

public export
grabType : OpSig
grabType = MkOpSig
  { Args = const ()
  , Arity = Ticky
  }

public export
emitType : OpSig
emitType = MkOpSig
  { Args = Ticky
  , Arity = const ()
  }

public export
waitType : OpSig
waitType = MkOpSig
  { Args = const ()
  , Arity = const ()
  }

public export
TSig : Signature
TSig = [
  grabType,
  emitType,
  waitType
]

%hint
TSigFunc : BoxCoalgSignature TSig
TSigFunc =
  [ -- grab
    MkFunOpSig { Args = BoxCoalgConst
               , Arity = BoxCoalgTicky
               }
  , -- emit
    MkFunOpSig { Args = BoxCoalgTicky
               , Arity = BoxCoalgConst
               }
  , -- wait
    MkFunOpSig { Args = BoxCoalgConst
               , Arity = BoxCoalgConst
               }
  ]

abst : (f -|> g) -> (f -% g).elem
abst alpha w' w'' [< rho, x] = alpha w'' x

unabst : (f -% g).elem -> (f -|> g)
unabst alpha w' x = alpha w' w' [< id, x]

export
grab : const () -|> TSig .Free Ticky
grab t _ = Op (TSig ?! 0) t [< (), abst pure t]

export
emit : Ticky -|> TSig .Free (const ())
emit t c = Op (TSig ?! 1) t [< c, abst pure t]

export
wait : const () -|> TSig .Free (const ())
wait t _ = Op (TSig ?! 2) t [< (), abst pure t]

data Timey : Time -> Type where
  Zy : Timey Z
  Sy : Timey n -> Timey (S n)

Clocked : Time -> Type
Clocked t = Timey t -> IO ()

BoxCoalgClocked : BoxCoalg Clocked
BoxCoalgClocked = MkBoxCoalg $ \t1, m, t2, le =>
  \ty =>
    case (ty, le) of
      (Zy, Now) => m ty
      ((Sy _), Now) => m ty
      ((Sy ty'), (Later le')) => BoxCoalgClocked .map le' m ty'

grabOp : FamProd [< Ticky -% Clocked, const ()] -|> Clocked
grabOp t [< cont, ()] = cont t [< Now, Clock 0]

emitOp : FamProd [< const () -% Clocked, Ticky] -|> Clocked
emitOp t [< cont, Clock i] = \ty => do
  printLn i
  cont t [< Now, ()] ty

waiting : (Le s -|> Clocked) -> (Le s -|> Clocked)
waiting cont t le ty = do
  putStrLn "waiting"
  getLine >>= \case
    "" => waiting cont (S t) (Later le) (Sy ty)
    _  => cont t le ty

waitOp : FamProd [< const () -% Clocked, const ()] -|> Clocked
waitOp t [< cont, ()] = waiting (\t', le => cont t' [< le, ()]) t Now

ClockedAlgebra : TSig .AlgebraOver Clocked
ClockedAlgebra = MkAlgebraOver [
  grabOp,
  emitOp,
  waitOp
]

MyProg : FamProd [< ] -|> TSig .Free (const ())
MyProg =           (\t, [< ]  =>
  grab _ () ) >>== (\t, [< x] =>
  wait _ () ) >>>> (\t, [< x] =>
  emit _ x  )

MyProg' : FamProd [< ] -|> TSig .Free (const ())
MyProg' =          (\t, [< ]  =>
  grab _ () ) >>== (\t, [< x] =>
  wait _ () ) >>>> (\t, [< x] =>
  grab _ () ) >>== (\t, [< x, y] =>
  emit _ x  ) >>>> (\t, [< x, y] =>
  emit _ y  ) >>>> (\t, [< x, y] =>
  wait _ () ) >>>> (\t, [< x, y] =>
  emit _ x  ) >>>> (\t, [< x, y] =>
  emit _ y  )

handle : TSig .Free (const ()) -|> Clocked
handle t comp = ClockedAlgebra .fold (\t', (), ty' => putStrLn "done") t comp

main : IO ()
main = handle Z (MyProg' Z [<]) Zy