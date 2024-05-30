module Paella.Presheaves.Basic

import Paella.Worlds
import Paella.Families
import Paella.Presheaves

%default total

-- Basic presheaves

||| The constant family is a presheaf
export
BoxCoalgConst : {t : Type} -> BoxCoalg (const t)
BoxCoalgConst = MkBoxCoalg $ \_, x, _, _ => x