module ExampleUniverse where

open import Reflection
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.Product
open import Data.Maybe
open import Data.Nat hiding (_<_ ; _>_) renaming (_≟_ to _≟-Nat_) 
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

open import Relation.Binary

data _<_ (m : ℕ) : ℕ → Set where
  <-base : m < suc m
  <-step : {n : ℕ} → m < n → m < suc n

-- module WF {A : Set} (_<_ : Rel A) where
-- 
--   data Acc (x : A) : Set where
--     acc : (∀ y → y < x → Acc y) → Acc x
-- 
--   Well-founded : Set
--   Well-founded = ∀ x → Acc x
-- 
-- open WF

open import Induction.WellFounded

<-ℕ-wf : Well-founded _<_
<-ℕ-wf x = acc (aux x)
  where
    aux : ∀ x y → y < x → Acc _<_ y
    aux zero y ()
    aux (suc x₁) .x₁ <-base = <-ℕ-wf x₁
    aux (suc x₁) y (<-step m) = aux x₁ y m
    
WTpack = Σ ℕ (λ n → Σ U' (λ u → Σ Ctx (λ g → WT g u n)))

to : ∀ {Γ σ n} → WT Γ σ n → WTpack
to {Γ}{σ}{n} wt = n , σ , Γ , wt

-- prove to . from = id

getEnv : WTpack → Ctx
getEnv (proj₁ , proj₂ , proj₃ , proj₄) = proj₃
getType : WTpack → U'
getType (proj₁ , proj₂ , proj₃ , proj₄) = proj₂
getSize : WTpack → ℕ
getSize (proj₁ , proj₂ , proj₃ , proj₄) = proj₁

from : ( p : WTpack) → WT (getEnv p) (getType p) (getSize p)
from (p1 , p2 , p3 , p4 ) = p4

sz : WTpack → ℕ
sz (proj₁ , proj₂ , proj₃ , proj₄) = proj₁

module <-on-sz-Well-founded where
  open Inverse-image {_} {WTpack} {ℕ} {_<_} sz public
  
  _≺_ : Rel WTpack _
  x ≺ y = sz x < sz y

  wf : Well-founded _≺_
  wf = well-founded <-ℕ-wf

s<s : ∀ {a b} → a < b → suc a < suc b
s<s <-base = <-base
s<s (<-step y) = <-step (s<s y)


module TLemma where

  _≼_ : Rel WTpack _
  x ≼ y = sz x < (1 + sz y)

  shift-pack-size : ∀ {τ Γ Γ' σ n} → (x : WT (Γ' ++ Γ) σ n) → to (weak {Γ'}{σ}{Γ} x τ) ≼ to x
  shift-pack-size (Var x) = <-base
  shift-pack-size (x ⟨ x₁ ⟩) = s<s <-base
  shift-pack-size (Lam σ x) = s<s <-base
  shift-pack-size (Lit x₁) = <-base

triv : ∀ {n m} → n < suc (n + m)
triv {zero} {zero} = <-base
triv {zero} {suc m} = <-step triv
triv {suc n} {m} = s<s triv

triv2 : ∀ {n m} → n < suc (m + n)
triv2 {n} {zero} = <-base
triv2 {n} {suc m} = <-step (triv2 {n}{m})

open <-on-sz-Well-founded ; open TLemma

allTsAcc : forall {Γ σ n} → (wt : WT Γ σ n) → Acc _≺_ (to wt) → TAcc wt
allTsAcc (Var x) _ = TBaseVar
allTsAcc (Lit x₁) _ = TBaseLit
allTsAcc {Γ} {τ => σ}{suc n} (Lam .τ wt) (acc x) = TLam (allTsAcc (shift1 (Cont σ) wt) (x (to (shift1 (Cont σ) wt)) <-base))
allTsAcc (_⟨_⟩ {Γ}{σ}{σ₁}{n}{m} wt wt₁) (acc x) = TApp (allTsAcc wt (x (to wt) triv))
                                                       (allTsAcc (shift1 (σ => σ₁) wt₁) (x (to (shift1 (σ => σ₁) wt₁)) (triv2 {_}{n})) )

finally : ∀{Γ σ n} → (wt : WT Γ σ n) → TAcc wt
finally wt = allTsAcc wt (wf (to wt))



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

-- -- we can also quote terms, CPS transform them,
-- -- then unquote them back into usable functions. cool!

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
test1 = T typedtest0 (finally typedtest0) id1

test1concrete :          lam2type test1
test1concrete = unquote (lam2term test1)
