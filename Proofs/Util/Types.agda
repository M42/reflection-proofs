module Proofs.Util.Types where

open import Data.String
open import Data.Bool
open import Data.Unit
open import Data.Nat

-- this is isomorphic to the empty (⊥) type,
-- but annotated with a message, which is nice for
-- attempting to report problems to the user.
data Error (a : String) : Set where

So : String → Bool → Set
So _ true  = ⊤
So s false = Error s

-- we can now use the P() function to wrap concrete
-- boolean formulæ. It just translates a boolean value
-- into it's propositional equivalent — inhabited (⊤) means
-- it's true, uninhabited (⊥) means false.
P : Bool → Set
P = So "Argument expression does not evaluate to true."

-- very much like ⊥-elim, but for Errors. in fact, this is
-- pretty much copied from the Agda standard library, Data.Empty module.
Error-elim : ∀ {Whatever : Set} {e : String} → Error e → Whatever
Error-elim ()




data Diff : ℕ → ℕ → Set where
  Base : ∀ {n}   → Diff n n
  Step : ∀ {n m} → Diff (suc n) m → Diff n m


