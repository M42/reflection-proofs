module ExampleTypeCheck where

open import Data.Nat

data ExampleUniverse : Set where
  Number : ExampleUniverse

U = ExampleUniverse

Uel : U → Set
Uel Number = ℕ

open import Equal

open import Data.Nat renaming (_≟_ to _≟-Nat_)
open import Data.Bool
open import Data.List


equal? : (x : U) → (y : U) → Equal? x y
equal? Number Number = yes

open import Reflection
open import Relation.Nullary.Core
open import Data.Maybe

type? : Name → Maybe U
type? n with n ≟-Name (quote ℕ)
type? n | yes p = just Number
type? n | no ¬p = nothing

quoteVal : (x : U) → Term → Uel x
quoteVal Number (var x args) = 0
quoteVal Number (con c args) with c ≟-Name quote zero
quoteVal Number (con c args) | yes p = 0
quoteVal Number (con c args) | no ¬p with c ≟-Name quote suc
quoteVal Number (con c [])   | no ¬p | yes p = 0
quoteVal Number (con c (arg v r x ∷ args)) | no ¬p | yes p = 1 + quoteVal Number x
quoteVal Number (con c args) | no ¬p₁ | no ¬p = 0
quoteVal Number      _       = 0

import Datatypes
open module DT = Datatypes U equal? Uel
import TypeCheck
open module TC = TypeCheck ExampleUniverse equal? type? Uel quoteVal 

idrep : forall {σ} → WT [] (σ => σ)
idrep = Lam _ (Var here) -- polymorphism!

f : WT [] ((O Number => O Number) => (O Number => O Number))
f = Lam (O Number => O Number) (Lam (O Number) ((Var (there here)) ⟨ Var here ⟩ ))

rawtest : Raw
rawtest = Lam (O Number => O Number) (Lam (O Number) (App (Var 1) (Var 0)))

testgoal0 : Raw -- :: a -> a
testgoal0 = term2raw (quoteTerm λ (b : ℕ) → ((λ (x : ℕ -> ℕ) → x)  λ (y : ℕ) → y) b)

testgoal1 : Raw -- :: (a -> b) -> (a -> b)
testgoal1 = term2raw (quoteTerm λ (b : ℕ → ℕ) → (λ (x : ℕ) → b x))

testgoal2 : Raw -- :: a -> b -> a
testgoal2 = term2raw (quoteTerm λ (b : ℕ) → (λ (x : ℕ) → b))

typedgoal0 : WT [] (typeOf testgoal0)
typedgoal0 = raw2wt testgoal0

typedgoal1 : WT [] (typeOf testgoal1)
typedgoal1 = raw2wt testgoal1

typedgoal2 : WT [] (typeOf testgoal2)
typedgoal2 = raw2wt testgoal2


--------------
-- examples --
--------------

untyped = term2raw (quoteTerm (\ (x : ℕ -> ℕ) -> x))

someTerm : WT [] (typeOf untyped)
someTerm = raw2wt untyped
