module Metaprogramming.ExampleTypeCheck where

open import Data.Nat
open import Data.List
open import Reflection

open import Relation.Binary.PropositionalEquality
open import Metaprogramming.ExampleUniverse
open DT
open TC


open import Metaprogramming.ExampleCPS
{-

This module will illustrate how to convert from Agda concrete code (lambda terms)
to the WT datatype, which is a well-typed, well-scoped model of lambda calculus.

The examples don't necessarily show how type inference is done, but merely
illustrate the use of the Metaprogramming.TypeCheck module.
-}

-- to get a feel for the WT datatype, here are some examples:
-- an identity function:
idrep : forall {σ} → WT [] (σ => σ) 2
idrep {σ} = Lam σ (Var here) -- polymorphism!

-- some function which, given an operation on naturals, and a natural,
-- returns the result. can be seen as a specialisation of _$_ in haskell.
f : WT [] ((O Nat => O Nat) => O Nat => O Nat) _
f = Lam (O Nat => O Nat) (Lam (O Nat) (Var (there here) ⟨ Var here ⟩ ))

-- quoting is done as follows. Note that the first result is a term of type
-- Raw, which is an annotated but type-unsafe lambda term, with possibly
-- out-of-scope variables.
testgoal0 : Raw -- :: n -> (n -> n) -> n
testgoal0 = term2raw (quoteTerm λ (b : ℕ) → ((λ (x : ℕ -> ℕ) → x)  λ (y : ℕ) → y) b)

-- note that it is necessary to annotate the arguments to the
-- abstractions with types, otherwise our type inference will fail.
-- because these annotations are mandatory, even the term2raw function will
-- fail, since it is pointless to return a Raw which isn't annotated.
testgoal1 : Raw -- :: (n -> n) -> n -> n
testgoal1 = term2raw (quoteTerm λ (b : ℕ → ℕ) → (λ (x : ℕ) → b x))

testgoal2 : Raw -- :: n -> n -> n
testgoal2 = term2raw (quoteTerm λ (b : ℕ) → (λ (x : ℕ) → b))

-- here we convert the above quoted terms into WT's
-- inspect with C-c C-n typedgoal0
-- or C-c C-n show typedgoal0
typedgoal0 : WT [] (typeOf testgoal0) _
typedgoal0 = raw2wt testgoal0

-- here is a nice helper to show you the WT lambda terms
-- without instantaneously causing your eyes to bleed:
open import Metaprogramming.Util.ExampleShow
pretty = show typedgoal0

typedgoal1 : WT [] (typeOf testgoal1) _
typedgoal1 = raw2wt testgoal1

typedgoal2 : WT [] (typeOf testgoal2) _
typedgoal2 = raw2wt testgoal2

-- we can reflect this back to "concrete" Agda; the function
-- is the same as the original term in testgoal1
concrete :          lam2type typedgoal1
concrete = unquote (lam2term typedgoal1)

unittest : concrete ≡ (λ (a : ℕ → ℕ) → λ (b : ℕ) → a b)
unittest = refl

-- note that types are preserved.
-- unittest0 : arrowconcrete ≡ (\ (a : Bool → Bool) → \ (b : Bool) → a b)
-- unittest0 = ?
-- wouldn't work.

-- and that's all there is to it, folks!
