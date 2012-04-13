module Lemmas where

open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Data.Bool
open import Data.Sum
open import Data.Product

-- these helpers show that a AND b => both a = true, as well as b = true.
and-l : ∀ {b b'} → b ∧ b' ≡ true → b ≡ true
and-l {true} eq = refl
and-l {false} eq = eq

and-r : ∀ b b' → b ∧ b' ≡ true → b' ≡ true
and-r true b' eq = eq
and-r false true eq = refl
and-r false false eq = eq

and-false : ∀ p q → p ∧ q ≡ false → p ≡ false ⊎ q ≡ false
and-false false q = inj₁
and-false true q  = inj₂

or-false : ∀ p q → p ∨ q ≡ false → p ≡ false × q ≡ false
or-false true  q ()
or-false false q pf = refl , pf

or-lem : ∀ p q → p ∨ q ≡ true → p ≡ true ⊎ q ≡ true
or-lem true q  = inj₁
or-lem false q = inj₂

not-lemma : {b : Bool} → not b ≡ true → b ≡ false
not-lemma {false} refl = refl
not-lemma {true}  ()

not-false : {b : Bool} → not b ≡ false → b ≡ true
not-false {true}  pf = refl
not-false {false} ()

