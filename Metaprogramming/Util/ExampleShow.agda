module Metaprogramming.Util.ExampleShow where

open import Data.String
open import Data.Nat

open import Metaprogramming.ExampleUniverse
open DT
open CPS'

{-

One might wonder why this seemingly universally-useful showing code
isn't in, say, the Datatypes module. The reason for this is that the
Datatypes module, where WT resides, is parameterised, since in the Lit
constructor it may contain an arbitrary user-chosen type. This
introduces difficulties when defining show, since the BUILTIN INTEGER
pragma may not be used in a parameterised module. If one then works
around that and puts the builtin-integer bit elsewhere, the results
still aren't satisfactory, since the output is the cluttered with
fully-qualified function names, such as
Metaprogramming.Util.Show.primStringAppend ...

Therefore, this function only works for the ExampleUniverse.
-}

{- a bit of code to make WT-terms a lot easier to look at. -}

-- the inspiration for this code comes from:
--      http://code.haskell.org/Agda/examples/Introduction/Built-in.agda

postulate
  Int    : Set
{-# BUILTIN INTEGER Int    #-}

primitive
  -- Integer functions
  primNatToInteger    : ℕ → Int
  primShowInteger     : Int → String

showℕ : ℕ → String
showℕ = λ x → primShowInteger (primNatToInteger x)

show : ∀ {Γ σ n} → WT Γ σ n → String
show (Var x)      = "$" ++ showℕ (index x)
show (wt ⟨ wt₁ ⟩) = show wt ++ " ⟨ " ++ show wt₁ ++ "⟩"
show (Lam σ wt)   = "(λ. " ++ show wt ++ ")"
show (Lit x₁)     = "literal" -- we don't print literal values, since we
                              -- have no idea what type they have right now.

{- end printing code -}

