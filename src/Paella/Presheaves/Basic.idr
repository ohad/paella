module Paella.Presheaves.Basic

import Paella.Worlds
import Paella.Families
import Paella.Presheaves

-- Basic presheaves

||| The constant family is a presheaf
public export
BoxCoalgConst : {t : Type} -> BoxCoalg (const t)
BoxCoalgConst = MkBoxCoalg $ \_, x, _, _ => x

||| The family of variables of type `a` is a presheaf
public export
BoxCoalgVar : {a : A} -> BoxCoalg (Var a)
BoxCoalgVar = MkBoxCoalg $ \w, pos, w', rho => rho a pos