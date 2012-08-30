module Metaprogramming.ExampleTypeCheck where

open import Data.Nat

open import Metaprogramming.Util.Equal

open import Data.Nat renaming (_≟_ to _≟-Nat_)
open import Data.Bool
open import Data.List

open import Reflection
open import Relation.Nullary.Core
open import Data.Maybe

open import Metaprogramming.ExampleUniverse
open DT
open TC

idrep : forall {σ} → WT [] (σ => σ) 2
idrep = Lam _ (Var here) -- polymorphism!

f : WT [] ((O Nat => O Nat) => (O Nat => O Nat)) _
f = Lam (O Nat => O Nat) (Lam (O Nat) ((Var (there here)) ⟨ Var here ⟩ ))

rawtest : Raw
rawtest = Lam (O Nat => O Nat) (Lam (O Nat) (App (Var 1) (Var 0)))

testgoal0 : Raw -- :: a -> a
testgoal0 = term2raw (quoteTerm λ (b : ℕ) → ((λ (x : ℕ -> ℕ) → x)  λ (y : ℕ) → y) b)

testgoal1 : Raw -- :: (a -> b) -> (a -> b)
testgoal1 = term2raw (quoteTerm λ (b : ℕ → ℕ) → (λ (x : ℕ) → b x))

testgoal2 : Raw -- :: a -> b -> a
testgoal2 = term2raw (quoteTerm λ (b : ℕ) → (λ (x : ℕ) → b))

typedgoal0 : WT [] (typeOf testgoal0) _
typedgoal0 = raw2wt testgoal0

typedgoal1 : WT [] (typeOf testgoal1) _
typedgoal1 = raw2wt testgoal1

typedgoal2 : WT [] (typeOf testgoal2) _
typedgoal2 = raw2wt testgoal2


--------------
-- examples --
--------------

untyped = term2raw (quoteTerm (\ (x : ℕ -> ℕ) -> x))

someTerm : WT [] (typeOf untyped) _
someTerm = raw2wt untyped
