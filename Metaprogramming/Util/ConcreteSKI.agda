module Metaprogramming.Util.ConcreteSKI where

{-
these are simply concrete Agda implementations of the SKI
combinators, which we can use when translating Comb -> Term.
It saves us building the corresponding lambda terms by hand,
and also ensures a certain amount of type-safety (since we can
verify once and for all, here, that the types of s, k and i
are correct).

See how they are used in Metaprogramming.SKI.
-}

s : ∀ {a b c : Set} → (a → b → c) → (a → b) → a → c
s f g x = f x (g x)

k : ∀ {a b : Set} → a → b → a
k c v = c

i : ∀ {a : Set} → a → a
i x = x
