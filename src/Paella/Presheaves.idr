module Paella.Presheaves

import Paella.Worlds
import Paella.Families

%default total

--------------------------------------------
-- The category of presheaves over worlds --
--------------------------------------------

-- Our presheaves do not have proof of functorial action attached to them since
-- we perform no proofs elsewhere

||| A family is a presheaf when equipped with a functorial action
public export 0
PresheafOver : p.family -> Type
PresheafOver f = {w1, w2 : p.world} -> (rho : w1 ~> w2) -> (f w1 -> f w2)

public export
infixr 1 =|>

namespace Coalgebra
  ||| A presheaf structure given in end form
  ||| The right-adjoint Fiore-transform comonad (Box)
  public export 0
  Box : p.family -> p.family
  Box f a = (b : p.world) -> (a ~> b) -> f b

  ||| Fiore transform: a `BoxCoalg` (with laws) is equivalent to a presheaf
  ||| (with laws)
  public export
  record BoxCoalg (f : p.family) where
    constructor MkBoxCoalg
    next : f -|> Box f

  ||| A `BoxCoalg` gives a functorial action
  export
  (.map) : {0 f : p.family} -> BoxCoalg f -> PresheafOver f
  coalg.map {w1,w2} rho v = coalg.next w1 v w2 rho

  ||| A coalgebra map, if we had laws this would be the same as a natural
  ||| transformation
  public export 0
  (=|>) : {f, g : p.family} -> (fAlg : BoxCoalg f) -> (gAlg : BoxCoalg g) -> Type
  (=|>) {f, g} _ _ = f -|> g

||| A functorial action for a family induces a box coalgebra
export
{f : _} -> Cast (PresheafOver f) (BoxCoalg f) where
  cast psh = MkBoxCoalg $ \w, x, w', rho => psh rho x

||| A box coalgebra for a family induces a functorial action
export
{f : _} -> Cast (BoxCoalg f) (PresheafOver f) where
  cast coalg = coalg.map
