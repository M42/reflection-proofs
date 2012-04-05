module Bool where

open import Relation.Binary.PropositionalEquality

data Propo : Set where
  T : Propo
  F : Propo

_∧_ : Propo -> Propo -> Propo
T ∧ b = b
F ∧ b = F

_∨_ : Propo -> Propo -> Propo
T ∨ b = T
F ∨ b = b

¬_ : Propo -> Propo
¬ T = F
¬ F = T

TisnotnotT : T ≡ ¬ ( ¬ T)
TisnotnotT = refl

pisnotnotp : {p : Propo} -> p ≡ ¬(¬ p)
pisnotnotp {T} = refl
pisnotnotp {F} = refl

