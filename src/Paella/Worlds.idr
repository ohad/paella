module Paella.Worlds

%default total

-- Omega
public export
data Time = Z | S Time

public export
World : Type
World = Time

public export
data Le : Time -> Time -> Type where
  Now : Le t t
  Later : Le s t -> Le s (S t)

public export
infixr 1 ~>

public export
(~>) : (src, tgt : World) -> Type
(~>) = Le

||| Identity renaming
export
id : t ~> t
id = Now

||| Composition of renamings
export
(.) : t2 ~> t3 -> t1 ~> t2 -> t1 ~> t3
(.) Now le = le
(.) (Later le1) le2 = Later (le1 . le2)