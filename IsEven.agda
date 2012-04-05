module IsEven where

open import Relation.Binary.PropositionalEquality
open import Data.Bool

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat
  
{-# BUILTIN NATURAL Nat #-} 
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     succ #-}

_+_ : Nat → Nat → Nat
0      + m = m
succ n + m = succ (n + m)

-- here we have the property of evenness on natural numbers
-- zero is even              <- rule
-- n is even => n+2 is even  <- rule
data Even  : Nat → Set where
  isEvenZ  : Even 0
  isEvenSS : {n : Nat} → Even n → Even (2 + n)
  
-- we want to prove that 2*n is always even, \forall n.

-- therefore, first make a decision function which tells us
-- if a given N is even
isEvenQ : Nat → Bool
isEvenQ 0 = true
isEvenQ 1 = false
isEvenQ (succ (succ n)) = isEvenQ n

-- now prove that N is even precisely when our function
-- returns True
soundIsEvenQ : {n : Nat} → isEvenQ n ≡ true → Even n
soundIsEvenQ {0} refl          = isEvenZ
soundIsEvenQ {1} ()
soundIsEvenQ {succ (succ n)} s = isEvenSS (soundIsEvenQ s)

-- now we can prove instances by applying the soundness theorem
-- with reflexivity proofs

-- For example, it turns out that 28 is even:
isEven28 : Even 28
isEven28 = soundIsEvenQ refl

-- or something which would otherwise have a rather large proof tree
isEven8772 : Even 8772
isEven8772 = soundIsEvenQ refl

