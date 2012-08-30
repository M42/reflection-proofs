module Metaprogramming.Apply where

-- ugh, this may not be in a parameterised module. if it is, such as
-- where it was in CPS.Apply, if you import CPS as CPS' = CPS . . . e.g.
-- then there's a panic, since `quote Apply` returns CPS.Apply, and all of
-- a sudden the number of arguments is invalid. ugh.
Apply : {A B : Set} → (A → B) → A → B
Apply {A} {B} x y = x y


open import Reflection

pleaseinfer : Type
pleaseinfer = el unknown unknown

