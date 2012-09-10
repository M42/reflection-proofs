module Metaprogramming.Util.Equal where

-- equality of types. No difference from
-- the equivalent definition in Relation.Binary.Core, except
-- this allows dot-patterns after decidable equality in Metaprogramming.TypeCheck.
data Equal? {A : Set} : A → A → Set where
  yes  : ∀ {τ}     → Equal? τ τ
  no   : ∀ {σ τ}   → Equal? σ τ

