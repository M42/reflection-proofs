module Proofs.IsEven where

open import Data.Empty
open import Data.Unit
open import Data.Nat

-- here we have the property of evenness on ℕ
-- zero is even              <- rule
-- n is even => n+2 is even  <- rule
data Even  : ℕ → Set where
  isEvenZ  : Even 0
  isEvenSS : {n : ℕ} → Even n → Even (2 + n)
  
-- we want to prove that some m = 2*n is even, ∀ m

-- therefore, first make a decision function which tells us
-- if a given n is even. what it's actually telling us, is
-- if the proof Even n is inhabited for a given n.
even? : ℕ → Set
even? 0             = ⊤
even? 1             = ⊥
even? (suc (suc n)) = even? n

-- now prove that n is even precisely when our function
-- returns true
soundnessEven : {n : ℕ} → even? n → Even n
soundnessEven {0} tt          = isEvenZ
soundnessEven {1} ()   -- this case is absurd; 1 isn't even
soundnessEven {suc (suc n)} s = isEvenSS (soundnessEven s)

-- now we can prove instances by applying the soundness theorem
-- with unit proofs

-- For example, it turns out that 28 is even:
isEven28 : Even 28
isEven28 = soundnessEven tt

-- or something which would otherwise have a rather large proof tree;
-- you can try to normalise one of these terms using C-c C-n isEven28 for
-- example, to see that an actual proof object is created.
isEven8772 : Even 8772
isEven8772 = soundnessEven tt

-- on the other hand, one might think we can trick the system,
-- trying to prove something uneven is even. This fails, however, since
-- we've shown above that the proposition that uneven naturals are even, is
-- isomorphic to ⊥, i.e. contains no elements.

-- another unfortunate thing is that this hole expects something
-- of type ⊥ -- we'll make the "error" nicer down below.
isEven27 : Even 27
isEven27 = soundnessEven {!!}

-- it's unfortunate that we have to include explicit proofs each time,
-- especially since they're always tt or impossible. We can use a trick
-- here to hide them (using implicit arguments). See the section in the thesis
-- for explanation on why this works.

sound : {n : ℕ} → {pf : even? n} → Even n
sound {0}           {tt} = isEvenZ
sound {1}           {()}
sound {suc (suc n)} {s } = isEvenSS (sound {n}{s})

-- now all we need to do is call `sound` -- the rest is inferred! this
-- makes for much neater proof objects.
isEven58 : Even 58
isEven58 = sound

{- We will now show how to give meaningful error messages
   if a number is odd. Unfortunately we have to use bools as a
   proxy, since otherwise the only error we would ever get is
   NotEven 1.
   -}
open import Data.Bool
open import Relation.Binary.PropositionalEquality

-- our ornamented error type
data NotEven : ℕ → Set where

evenB? : ℕ → Bool
evenB? zero = true
evenB? (suc zero) = false
evenB? (suc (suc n)) = evenB? n

-- check if a number is even. If so, give top,
-- else return our error type, with the number
-- as an argument
soEven : ℕ → Set
soEven n = if evenB? n then ⊤ else NotEven n

-- now prove that n is even precisely when our function
-- returns true
soundnessEven' : {n : ℕ} → {p : evenB? n ≡ true} → Even n
soundnessEven' {0} {e} = isEvenZ
soundnessEven' {suc zero} {()}
soundnessEven' {suc (suc n)} {s} = isEvenSS (soundnessEven' {n} {s})

decEven : {n : ℕ} → {p : soEven n} → Even n
decEven {n} {p}    with evenB? n    | inspect evenB? n
decEven {n}        | true           | [ eq ]    = soundnessEven' {n} {eq}
decEven {n} {()}   | false          | [ eq ]

-- now we can prove instances by applying the soundness theorem
-- with reflexivity proofs

-- For example, it turns out that 30 is even:
isEven30 : Even 30
isEven30 = decEven

-- ...but 13 throws a _descriptive_ error!
isEven13 : Even 13
isEven13 = decEven