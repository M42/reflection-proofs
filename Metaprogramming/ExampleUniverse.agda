module Metaprogramming.ExampleUniverse where

open import Reflection
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.Product
open import Data.Maybe
open import Data.Nat hiding (_<_ ; _>_) renaming (_≟_ to _≟-Nat_) 
open import Metaprogramming.Util.Equal
open import Relation.Nullary.Core
open import Induction.WellFounded

--- THIS STUFF may not be used other than as parameters to the modules.

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

-- end THIS STUFF
------------------------

-- now define aliases for the modules
import Metaprogramming.Datatypes
open module DT = Metaprogramming.Datatypes U equal? Uel
import Metaprogramming.TypeCheck
open module TC = Metaprogramming.TypeCheck U equal? type? Uel quoteVal quoteBack
import Metaprogramming.CPS
open module CPS' = Metaprogramming.CPS U Uel equal? type? quoteBack halttype
import Metaprogramming.SKI
open module SKI' = Metaprogramming.SKI U equal? type? Uel quoteVal quoteBack

-- notice how we can quote a term, automatically getting
-- a well-typed lambda
arrow : Term
arrow = quoteTerm (\ (x : ℕ → ℕ) → \ (y : ℕ) → x y)

wtarrow : WT [] (typeOf (term2raw arrow)) (sizeOf (term2raw arrow))
wtarrow = raw2wt (term2raw arrow)

-- we can reflect this back to "concrete" Agda; the function
-- is the same as the original term in arrow
arrowconcrete :          lam2type wtarrow
arrowconcrete = unquote (lam2term wtarrow)

unittest : arrowconcrete ≡ (λ (a : ℕ → ℕ) → λ (b : ℕ) → a b)
unittest = refl

open import Data.Bool hiding (T)

-- note that types are preserved.
-- unittest0 : arrowconcrete ≡ (\ (a : Bool → Bool) → \ (b : Bool) → a b)
-- unittest0 = ?
-- that wouldn't work.

-- we can also quote terms, CPS transform them,
-- then unquote them back into usable functions. cool!

g : Raw
g = term2raw (quoteTerm (λ (n : ℕ) → n))
a : Raw
a = term2raw (quoteTerm 7)

test0 : Raw
test0 = App g a

typedtest0 : WT [] (typeOf test0) (sizeOf test0)
typedtest0 = raw2wt test0

viewTypedTest0 : typedtest0 ≡ Lam (O Nat) (Var here) ⟨ Lit 7 ⟩
viewTypedTest0 = refl

id1 : ∀ {Γ σ} → WT Γ (σ => σ) 2
id1 = Lam _ (Var here)

test1 : WT [] RT _
test1 = T typedtest0 id1

-- test1concrete :          lam2type test1
-- test1concrete = unquote (lam2term test1)
