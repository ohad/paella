module Paella.Families

import Paella.Worlds

%default total

public export
Family : Type
Family = World -> Type

infixr 1 -|>
infixr 9 .

||| Family transformation, i.e. a morphism of families
public export
(-|>) : (f, g : Family) -> Type
f -|> g = (w : World) -> f w -> g w

||| Given a family `f`, gives `1 -|> f` i.e. generalized elements
public export
(.elem) : (f : Family) -> Type
f.elem = (w : World) -> f w

||| Identity family transformation
export
id : {f : Family} -> f -|> f
id w x = x

||| Composition of family transformations
export
(.) : {f, g, h : Family} -> (g -|> h) -> (f -|> g) -> (f -|> h)
(beta . alpha) w = beta w . alpha w