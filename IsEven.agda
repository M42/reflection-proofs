module IsEven where

open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Nat

-- here we have the property of evenness on ℕ
-- zero is even              <- rule
-- n is even => n+2 is even  <- rule
data Even  : ℕ → Set where
  isEvenZ  : Even 0
  isEvenSS : {n : ℕ} → Even n → Even (2 + n)
  
-- we want to prove that 2*n is always even, ∀n.

-- therefore, first make a decision function which tells us
-- if a given n is even
isEvenQ : ℕ → Bool
isEvenQ 0 = true
isEvenQ 1 = false
isEvenQ (suc (suc n)) = isEvenQ n

-- now prove that n is even precisely when our function
-- returns true
soundIsEvenQ : {n : ℕ} → isEvenQ n ≡ true → Even n
soundIsEvenQ {0} refl          = isEvenZ
soundIsEvenQ {1} ()
soundIsEvenQ {suc (suc n)} s = isEvenSS (soundIsEvenQ s)

-- now we can prove instances by applying the soundness theorem
-- with reflexivity proofs

-- For example, it turns out that 28 is even:
isEven28 : Even 28
isEven28 = soundIsEvenQ refl

-- or something which would otherwise have a rather large proof tree
isEven8772 : Even 8772
isEven8772 = soundIsEvenQ refl

