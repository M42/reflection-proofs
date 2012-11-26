module Proofs.Util.Handy where

open import Data.Bool

-- simply a nice way of writing down implication. Classical logic.
infixr 4 _⇒_
_⇒_   : Bool → Bool → Bool
true  ⇒ true  = true
true  ⇒ false = false
false ⇒ true  = true
false ⇒ false = true

-- dependently typed if-statement. This was necessary because usually
-- if_then_else_ constructions require both T and F branches to return
-- the same type.
if : {P : Bool → Set} → (b : Bool) → P true → P false → P b
if true  t f = t
if false t f = f
