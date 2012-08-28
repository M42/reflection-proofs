module ExampleUniverse where

open import Reflection
open import Data.List
open import Data.Maybe
open import Data.Nat hiding (_<_)
open import Equal
open import Relation.Nullary.Core

---------
--- THIS STUFF may not be used other than as a parameter to the module.

data U : Set where
  Nat : U


?type : U → Name
?type r = quote ℕ

Uel : U → Set
Uel r = ℕ


quoteBack : (x : U) → Uel x → Term
quoteBack Nat zero    = con (quote zero) []
quoteBack Nat (suc x) = con (quote suc) (arg visible relevant (quoteBack Nat x) ∷ [])

equal? : (x : U) → (y : U) → Equal? x y
equal? Nat Nat = yes

halttype : U
halttype = Nat

type? : Name → Maybe U
type? n with n ≟-Name (quote suc)
type? n | yes p = just Nat
type? n | no ¬p with n ≟-Name (quote zero)
type? n | no ¬p | yes p = just Nat
type? n | no ¬p₁ | no ¬p with n ≟-Name (quote ℕ)
type? n | no ¬p₁ | no ¬p | yes p = just Nat
type? n | no ¬p₂ | no ¬p₁ | no ¬p = nothing

quoteVal : (x : U) → Term → Uel x
quoteVal Nat (var x args) = 0
quoteVal Nat (con c args) with c ≟-Name quote zero
quoteVal Nat (con c args) | yes p = 0
quoteVal Nat (con c args) | no ¬p with c ≟-Name quote suc
quoteVal Nat (con c []) | no ¬p | yes p = 0
quoteVal Nat (con c (arg v r x ∷ args)) | no ¬p | yes p = 1 + quoteVal Nat x
quoteVal Nat (con c args) | no ¬p₁ | no ¬p = 0
quoteVal Nat      _       = 0

-- result type.

-- end THIS STUFF
------------------------

import Datatypes
open module DT = Datatypes U equal? Uel
import TypeCheck
open module TC = TypeCheck U equal? type? Uel quoteVal quoteBack
import CPS
open module CPS' = CPS U Uel equal? type? quoteBack halttype

Rel : Set → Set₁
Rel A = A → A → Set


module WF where

  data _<_ (m : ℕ) : ℕ → Set where
    <-base : m < suc m
    <-step : {n : ℕ} → m < n → m < suc n

  measure : ∀ {Γ σ} → WT Γ σ → ℕ
  measure (Var x) = 1
  measure (wt ⟨ wt₁ ⟩) = 2 + measure wt + measure wt₁
  measure (Lam σ wt) = 1 + measure wt 
  measure (Lit x₁) = 1 

  data Acc {Γ : Ctx} {σ : U'} (x : WT Γ σ) : Set where
    acc : (∀ {Γ' σ'} (y : WT Γ' σ') → measure y < measure x → Acc y) → Acc x

  -- Well-founded : Set
  -- Well-founded = (∀ x → Acc x)


open WF
-- 
-- <-ℕ-wf : Well-founded _<_
-- <-ℕ-wf x = acc (aux x)
--   where
--     aux : ∀ x y → y < x → Acc _<_ y
--     aux .(suc y) y <-base = <-ℕ-wf y
--     aux .(suc x) y (<-step {x} y<x) = aux x y y<x

-- module Inverse-image-Well-founded {A B} (_<_ : Rel B) (f : A → B) where
-- 
--   _≺_ : Rel A
--   _≺_ x y = f x < f y
-- 
--   ii-acc : ∀ {x} → Acc _<_ (f x) → Acc _≺_ x
--   ii-acc (acc g) = acc (λ y fy<fx → ii-acc (g (f y) fy<fx))
-- 
--   ii-wf  : Well-founded _<_ → Well-founded _≺_
--   ii-wf wf x = ii-acc (wf (f x))

-- for the wt / T case:
-- _<_ : Rel ℕ
-- measure : Raw? → ℕ
-- _≺_ : Rel Raw

-- now we want to be able to compare distinct types with a same measure.
-- module Heterogeneous-Well-founded {A B C} (_<_ : Rel C) (f : A → C) (g : B → C) where

--   _≺_ : A → B → Set
--   _≺_ x y = f x < g y

--   ii-acc : ∀ {x} → Acc _<_ (f x) → Acc _≺_ x
--   ii-acc (acc g) = acc (λ y fy<fx → ii-acc (g (f y) fy<fx))

  -- ii-wf  : Well-founded _<_ → Well-founded _≺_
  -- ii-wf wf x = ii-acc (wf (f x))
  

-- measure : Raw    → ℕ
-- measure (Var x) = 1
-- measure (App wt wt₁) = measure wt + measure wt₁
-- measure (Lam σ wt) = 1 + measure wt
-- measure (Lit a x₁) = 1
-- 
-- module <-on-measure-Well-founded where
--   open Inverse-image-Well-founded {Raw} _<_ measure public
-- 
--   wf : Well-founded _≺_
--   wf = ii-wf <-ℕ-wf
-- 
-- 
-- module ShiftLemma where
_≼_ : forall {Γ Γ' σ} → WT Γ σ → WT Γ' σ → Set
x ≼ y = measure x < (1 + measure y)

s<s : ∀ {a b} → a < b → suc a < suc b
s<s <-base = <-base
s<s (<-step y) = <-step (s<s y)

iets2 : ∀ {n m m1} → m < m1 → (n + m) < (n + m1)
iets2 = {!!}

iets : ∀ {n m n₁ m₁} → n < suc n₁ → m < suc m₁ → (n + m) < (suc (n₁ + m₁))
iets <-base <-base = <-base
iets {n}{m}{.n}{m₁} <-base (<-step mm1) = <-step (iets2 {n}{m}{m₁} mm1)
iets (<-step nn1) mm1 = {!!}

shift-size : ∀ {τ Γ σ} → (x : WT Γ σ) → shift1 τ x ≼ x
shift-size (Var x)  = <-base
shift-size (Lit x₁) = <-base
shift-size {τ} (x ⟨ x₁ ⟩) with shift1 τ x | shift-size {τ} x | shift1 τ x₁ | shift-size {τ} x₁
... | a | b | c | d =  (s<s (s<s (iets b d)))
shift-size {τ} (Lam σ x) with shift1 τ x | shift-size {τ} x
... | a | b = s<s {!b!}

open import Relation.Binary.PropositionalEquality

measure>0 : ∀ {Γ : Ctx} {σ : U'} (wt : WT Γ σ) → 0 < measure wt
measure>0 (Var x) = <-base
measure>0 (wt ⟨ wt₁ ⟩) with measure>0 wt | measure>0 wt₁
... |  a | b = {!n<n+m+1!}
measure>0 (Lam σ wt) = <-step (measure>0 wt)
measure>0 (Lit x₁) = <-base

addExprs : forall {Γ σ Γ' σ'} → (wt : WT Γ σ) (n : WT Γ' σ') → measure wt < (2 + measure wt + measure n)
addExprs wr = {!cong-< ? ? ? !}

addExprsSym : forall {τ Γ σ Γ' σ'} → (wt : WT Γ σ) (n : WT Γ' σ') → measure (shift1 τ wt) < (2 + measure n + measure wt)
addExprsSym wt n = {!cong!}

-- termination/reachability for T algorithm.
allTsAcc : forall {Γ σ} → (wt : WT Γ σ) → Acc wt → TAcc wt
allTsAcc (Var x) _ = TBaseVar
allTsAcc (Lit x₁) _ = TBaseLit
allTsAcc {Γ} {τ => σ} (Lam .τ wt) (acc x) = TLam (allTsAcc (shift1 (Cont σ) wt) (x (shift1 (Cont σ) wt) (shift-size wt)))
allTsAcc (_⟨_⟩ {Γ}{σ}{σ₁} wt wt₁) (acc x) = TApp (allTsAcc wt (x wt (addExprs wt wt₁))) (allTsAcc (shift1 (σ => σ₁) wt₁) (x (shift1 (σ => σ₁) wt₁) (addExprsSym {σ => σ₁}{Γ}{σ} wt₁ wt) ) )


-- -- notice how we can quote a term, automatically getting
-- -- a well-typed lambda
-- arrow : Term
-- arrow = quoteTerm (\ (x : ℕ → ℕ) → \ (y : ℕ) → x y)

-- wtarrow : WT [] (typeOf (term2raw arrow))
-- wtarrow = raw2wt (term2raw arrow)

-- -- we can reflect this back to "concrete" Agda; the function
-- -- is the same as the original term in arrow
-- arrowconcrete :          lam2type wtarrow
-- arrowconcrete = unquote (lam2term wtarrow)

-- open import Relation.Binary.PropositionalEquality

-- unittest : arrowconcrete ≡ (λ (a : ℕ → ℕ) → λ (b : ℕ) → a b)
-- unittest = refl
-- -- note that types are preserved.
-- -- unittest0 : arrowconcrete ≡ (\ (a : Bool → Bool) → \ (b : Bool) → a b)
-- -- unittest0 = ?
-- -- that wouldn't work.

-- ---
-- -- we can also quote terms, CPS transform them,
-- -- then unquote them back into usable functions. cool!

-- g : Raw
-- g = term2raw (quoteTerm (λ (n : ℕ) → n))
-- a : Raw
-- a = term2raw (quoteTerm 7)

-- test0 : Raw
-- test0 = App g a

-- typedtest0 : WT [] (typeOf test0)
-- typedtest0 = raw2wt test0

-- viewTypedTest0 : typedtest0 ≡ Lam (O Nat) (Var here) ⟨ Lit 7 ⟩
-- viewTypedTest0 = refl

-- id1 : ∀ {Γ σ} → WT Γ (σ => σ)
-- id1 = Lam _ (Var here)

-- test1 : WT [] RT
-- test1 = T typedtest0 (allTsAcc typedtest0) id1

-- test1concrete :          lam2type test1
-- test1concrete = unquote (lam2term test1)
