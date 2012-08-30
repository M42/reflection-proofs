open import Metaprogramming.Util.Equal
open import Reflection
open import Data.Maybe

module Metaprogramming.WTWellfounded
           (U : Set)
           (equal? : (x : U) → (y : U) → Equal? x y)
           (Uel : U → Set)
           (type? : Name → Maybe U)
           (quoteBack : (x : U) → Uel x → Term)
           (ReturnType : U) where

open import Data.Nat hiding (_<_)
import Metaprogramming.Datatypes
open module DT = Metaprogramming.Datatypes U equal? Uel

open import Data.List
open import Relation.Binary
open import Induction.WellFounded

<-ℕ-wf : Well-founded _<_
<-ℕ-wf x = acc (aux x)
  where
    aux : ∀ x y → y < x → Acc _<_ y
    aux zero y ()
    aux (suc x₁) .x₁ <-base = <-ℕ-wf x₁
    aux (suc x₁) y (<-step m) = aux x₁ y m

module <-on-sz-Well-founded where
  open Inverse-image {_} {WTpack} {ℕ} {_<_} sz public

  _≺_ : Rel WTpack _
  x ≺ y = sz x < sz y

  wf : Well-founded _≺_
  wf = well-founded <-ℕ-wf

s<s : ∀ {a b} → a < b → suc a < suc b
s<s <-base = <-base
s<s (<-step y) = <-step (s<s y)

