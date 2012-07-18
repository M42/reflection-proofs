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
  
-- we want to prove that 2*n is even, ∀(2*n).

-- therefore, first make a decision function which tells us
-- if a given n is even
even? : ℕ → Bool
even? zero          = true
even? (suc zero)    = false
even? (suc (suc n)) = even? n

-- now prove that n is even precisely when our function
-- returns true
soundnessEven : {n : ℕ} → even? n ≡ true → Even n
soundnessEven {0} refl        = isEvenZ
soundnessEven {1} ()
soundnessEven {suc (suc n)} s = isEvenSS (soundnessEven s)

-- now we can prove instances by applying the soundness theorem
-- with reflexivity proofs

-- For example, it turns out that 28 is even:
isEven28 : Even 28
isEven28 = soundnessEven refl

-- or something which would otherwise have a rather large proof tree
isEven8772 : Even 8772
isEven8772 = soundnessEven refl


open import Data.Unit
open import Data.Empty

-- it's unfortunate that we have to include explicit proofs each time,
-- especially since they're always refl or impossible. We can use a trick
-- here to hide them (using implicit arguments).

even?' : ℕ → Set
even?' 0  = ⊤
even?' 1  = ⊥
even?' (suc (suc n)) = even?' n

sound : {n : ℕ} → {pf : even?' n} → Even n
sound {0} {tt} = isEvenZ
sound {1} {()}
sound {suc (suc n)} {s} = isEvenSS (sound {n}{s})

-- now all we need to do is call `sound` -- the rest is inferred!
isEven58 : Even 58
isEven58 = sound
