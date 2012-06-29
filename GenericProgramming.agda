module GenericProgramming where

open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.List
open import Reflection




open import Relation.Binary.PropositionalEquality

-- we want to convert this into a generic representation
data Random : Set where
  A : ℕ → ℕ → Random
  B : ℕ → Random


test : List Name
test = quoteGoal e in constructors {!primQNameDefinition!!}