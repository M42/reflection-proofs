module Metaprogramming.Util.Apply where

-- ugh, this may not be in a parameterised module. if it is, such as
-- where it was in CPS.Apply, if you import CPS as CPS' = CPS . . . e.g.
-- then there's a panic, since `quote Apply` returns CPS.Apply, and all of
-- a sudden the number of arguments is invalid. ugh.
-- anyway, this is used to introduce application when unquoting WT -> Term
Apply : {A B : Set} → (A → B) → A → B
Apply {A} {B} x y = x y

open import Reflection

-- this is used as a type argument to lam constructors when unquoting, since
-- Agda will infer the type anyway, which saves us going to the trouble of defining
-- a function U' → Type. This would also have meant requiring more pattern-matching
-- helper functions from the user on their U universe.
pleaseinfer : Type
pleaseinfer = el unknown unknown

