module Predicate where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

{- I only want my ℕ inputs to be successors so let's build
   a predicate IsSuc: -}

data IsSuc : ℕ → Set where
  YesItIs : ∀ n → IsSuc (suc n)

{- Predecessor is only defined on ℕs that are successors
   and, btw, it is correct. -}

Pred : ∀ {n} (pr : IsSuc n) → ℕ
Pred (YesItIs n) = n

Pred-is-pred : ∀ {n} pr → suc (Pred {n} pr) ≡ n
Pred-is-pred (YesItIs n) = refl


{- Now I can decide whether a ℕ is a suc or not -}

open import Relation.Nullary

IsSuc-dec : ∀ n → Dec (IsSuc n)
IsSuc-dec zero = no (λ ())
IsSuc-dec (suc n) = yes (YesItIs n)