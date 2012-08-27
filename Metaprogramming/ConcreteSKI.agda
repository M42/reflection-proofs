module ConcreteSKI where

s : ∀ {a b c : Set} → (a → b → c) → (a → b) → a → c
s f g x = f x (g x)

k : ∀ {a b : Set} → a → b → a
k c v = c

i : ∀ {a : Set} → a → a
i x = x