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
  isEvenSS : {n : Nat} → Even n → Even (n + n)
  
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
soundIsEvenQ = {!!}


-- now we can prove instances by applying the soundness theorem
-- with reflexivity proofs

isEven2N : {n : Nat} → Even (n + n)
isEven2N {n} = soundIsEvenQ {n + n} {!refl!}

