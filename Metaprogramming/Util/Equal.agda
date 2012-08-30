module Metaprogramming.Util.Equal where

-- equality of types.
data Equal? {A : Set} : A → A → Set where
  yes  : forall {τ}     → Equal? τ τ
  no   : forall {σ τ}   → Equal? σ τ

