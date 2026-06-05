module Paella.Families

import Paella.Worlds

%default total

------------------------------------------
-- The category of families over worlds --
------------------------------------------

||| A `Family` is a family of typs over worlds
public export
(.family) : Type -> Type
p.family = p.world -> Type

public export
infixr 1 -|>
public export
infixr 9 .

||| Family transformation, i.e. a morphism of families
public export 0
(-|>) : (f, g : p.family) -> Type
f -|> g = (w : p.world) -> f w -> g w

||| Given a family `f`, gives `1 -|> f` i.e. generalized elements
public export 0
(.elem) : (f : p.family) -> Type
f.elem = (w : p.world) -> f w

||| Identity family transformation
export
id : {0 f : p.family} -> f -|> f
id w x = x

||| Composition of family transformations
export
(.) : {0 f, g, h : p.family} -> (g -|> h) -> (f -|> g) -> (f -|> h)
(beta . alpha) w = beta w . alpha w
