module ExampleUniverse where

open import Reflection
open import Data.List
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

Rel : Set → Set₁
Rel A = A → A → Set


module WF where

  data _<_ (m : ℕ) : ℕ → Set where
    <-base : m < suc m
    <-step : {n : ℕ} → m < n → m < suc n
    
  data Acc {Γ : Ctx} {σ : U'} {n : ℕ} (x : WT Γ σ n) : Set where
    acc : (∀ {Γ' σ' n'} (y : WT Γ' σ' n') → n' < n → Acc y) → Acc x
-- 
--   Well-founded : Set
--   Well-founded = (∀ {Γ σ} x → Acc {Γ}{σ} x)
-- 
open WF
_≼_ : forall {Γ Γ' σ n m} → WT Γ σ n → WT Γ' σ m → Set
_≼_ {_}{_}{_}{n}{m} x y = n < (1 + m)

s<s : ∀ {a b} → a < b → suc a < suc b
s<s <-base = <-base
s<s (<-step y) = <-step (s<s y)

iets2 : ∀ {n m m1} → m < m1 → (n + m) < (n + m1)
iets2 {zero} {m} {suc .m} <-base = <-base
iets2 {suc n} {m} {suc .m} <-base = s<s (iets2 {n}{m}{suc m} <-base)
iets2 {zero} (<-step a) = <-step a
iets2 {suc n} (<-step a) = s<s (iets2 {n}{_}{_} (<-step a))


iets3 : ∀ {n m n₁} → n < n₁ → (n + m) < (n₁ + m)
iets3 {zero} {m} {suc .0} <-base = <-base
iets3 {suc n} {m} {suc .(suc n)} <-base = <-base
iets3 {zero} (<-step a) = <-step (iets3 a)
iets3 {suc n} (<-step a) = <-step (iets3 a)

iets4 : ∀ {n m nn mm} → n < nn → m < mm → (n + m) < (nn + mm)
iets4 {n}{m}{suc .n}{suc .m} <-base <-base = <-step (iets2 {n}{m}{suc m}<-base)
iets4 {zero} <-base (<-step b) = <-step (<-step b)
iets4 {suc n} <-base (<-step b) = <-step (s<s (iets2 {n} (<-step b)))
iets4 (<-step a) <-base = <-step (iets4 a <-base)
iets4 (<-step a) (<-step b) = <-step (iets4 a (<-step b))

iets : ∀ {n m n₁ m₁} → n < suc n₁ → m < suc m₁ → (n + m) < (suc (n₁ + m₁))
iets <-base <-base = <-base
iets {n}{m}{.n}{m₁} <-base (<-step mm1) = <-step (iets2 {n}{m}{m₁} mm1)
iets {n}{m}{n₁}{.m} (<-step nn1) <-base = <-step (iets3 nn1)
iets (<-step nn1) (<-step mm1) = <-step (iets4 nn1 mm1)

open import Relation.Binary.PropositionalEquality

allEqual : ∀ {Γ Γ' σ τ n} → (wt : WT (Γ' ++ Γ) σ n) → n ≡ wtSize (weak {Γ'} {σ} {Γ} wt τ)
allEqual (Var x)       = refl
allEqual {Γ}{Γ'}{σ}(_⟨_⟩ {.(Γ' ++ Γ)}{σ₁}{.σ} wt  wt₁ )  = cong suc refl
allEqual {Γ}{Γ'}{σ => τ}{τ₂}{suc n}(Lam .σ wt) = cong suc (allEqual {Γ}{σ ∷ Γ'}{τ}{τ₂}{n} wt)
allEqual (Lit x₁)      = refl

geez∈ : {A : Set} {x : A} → ∀{xs} → x ∈ xs → x ∈ (xs ++ [])
geez∈ here = here
geez∈ (there inn) = there (geez∈ inn)

geez : ∀{Γ σ n} → WT Γ σ n → WT (Γ ++ []) σ n
geez (Var x) = Var (geez∈ x)
geez (wt ⟨ wt₁ ⟩) = geez wt ⟨ geez wt₁ ⟩
geez (Lam σ wt) = Lam σ (geez wt)
geez (Lit x₁) = Lit x₁

shift-size : ∀ {τ Γ Γ' σ n} → (x : WT (Γ' ++ Γ) σ n) → weak {Γ'}{σ}{Γ} x τ ≼ x
shift-size (Var x)  = <-base
shift-size (Lit x₁) = <-base
shift-size {τ}{Γ}{Γ'} (x ⟨ x₁ ⟩) with shift-size {τ}{Γ}{Γ'} x | shift-size {τ}{Γ}{Γ'} x₁
... | b | d =  ((s<s (iets b d)))
shift-size {τ}{Γ}{Γ'}{τ₁ => σ} (Lam .τ₁ x) with shift-size {τ}{Γ}{τ₁ ∷ Γ'} x
shift-size {τ}{Γ}{Γ'}{τ₁ => σ} (Lam .τ₁ x) | b with geez x
... | eqq with allEqual {[]} {τ₁ ∷ (Γ' ++ Γ)} {σ} {τ₁} eqq
... | ss = s<s b

shift-weak : ∀ {Γ τ σ n} (wt : WT Γ τ n) → weak {[]} wt σ ≡ shift1 σ wt
shift-weak wt = refl

shift-weak2 : ∀ {Γ τ σ n} {wt : WT Γ τ n} → weak {[]} wt σ ≼ wt → shift1 σ wt ≼ wt
shift-weak2 {Γ} {τ} {σ} {wt} wk = wk

triv : ∀ {n m} → n < suc (n + m)
triv {zero} {zero} = <-base
triv {zero} {suc m} = <-step triv
triv {suc n} {zero} = s<s triv
triv {suc n} {suc m} = s<s triv

triv2 : ∀ {n m} → n < suc (m + n)
triv2 {n} {zero} = <-base
triv2 {n} {suc m} = <-step (triv2 {n}{m})

triv3 : ∀ {n m} → n < (2 + (m + n))
triv3 {zero} {zero} = <-step <-base
triv3 {suc n} {zero} = <-step <-base
triv3 {zero} {suc m} = <-step (triv3 {zero}{m})
triv3 {suc n} {suc m} = <-step (triv3 {suc n}{m})

addExprs : forall {Γ σ Γ' σ' szwt szn} → (wt : WT Γ σ szwt) (n : WT Γ' σ' szn) → szwt < (1 + szwt + szn)
addExprs wr n = triv

addExprsSym : forall {Γ σ Γ' σ' szwt szn} → (wt : WT Γ σ szwt) (n : WT Γ' σ' szn) → szwt < (1 + szn + szwt)
addExprsSym {Γ}{σ}{Γ'}{σ'}{szwt}{szn} wt n = triv2 {szwt}{szn}


-- termination/reachability for T algorithm.

-- allTsAccℕ : forall {Γ σ n} → {szn : Add n} → (wt : WT Γ σ n) → TAccℕ wt szn
-- allTsAccℕ {_}{_}{1}{szn} (Var x)  = ?
-- allTsAccℕ (Lit x₁)  = ?
-- allTsAccℕ {Γ} {τ => σ}{suc n} (Lam .τ wt)  = ?
-- allTsAccℕ {_}{.σ₁}{.(suc n + m)}(_⟨_⟩ {._}{σ}{σ₁}{n}{m} wt wt₁) = ?

allTsAcc : forall {Γ σ n} → (wt : WT Γ σ n) → Acc wt → TAcc wt
allTsAcc (Var x) _ = TBaseVar
allTsAcc (Lit x₁) _ = TBaseLit
allTsAcc {Γ} {τ => σ}{suc n} (Lam .τ wt) (acc x) = TLam (allTsAcc (shift1 (Cont σ) wt) (x (shift1 (Cont σ) wt) (shift-weak2 {τ ∷ Γ}{σ}{Cont σ}{n}{wt} (shift-size {Cont σ}{τ ∷ Γ}{[]} wt))))
allTsAcc (_⟨_⟩ {Γ}{σ}{σ₁}{n}{m} wt wt₁) (acc x) = TApp (allTsAcc wt (x wt (addExprs wt wt₁))) (allTsAcc (shift1 (σ => σ₁) wt₁) (x (shift1 (σ => σ₁) wt₁) (addExprsSym {Γ}{σ}{_}{_}{m}{n} wt₁ wt) ) )





mutual
  aux : (Γ : Ctx) (σ : U') {n : ℕ} → ∀ {Γ'}{σ'}{n'} (x : WT Γ σ n) (y : WT Γ' σ' n') → n' < n → Acc y
  aux Γ σ (Var x) () <-base
  aux Γ σ (Var x) y (<-step ())
  aux Γ σ {.(suc (n + m))} (_⟨_⟩ {._}{_}{._}{n}{m} x x₁) y <-base = acc (λ {Γ'}{σ'}{n'} y₁ x₂ → aux {!!} {!!} {!!} {!!} x₂)
  aux Γ σ (x ⟨ x₁ ⟩) y (<-step m₁) = acc (λ {Γ'}{σ'}{n'} y₁ x₂ → aux {!!} {!!} {!!} {!!} {!m₁!})
  aux Γ .(σ => τ) (Lam σ {τ} x) y m = {!!}
  aux Γ .(O x) (Lit {.Γ} {x} x₁) () <-base
  aux Γ .(O x) (Lit {.Γ} {x} x₁) y (<-step ())

  wf : ∀ (Γ : Ctx) (σ : U') {n : ℕ} → (wt : WT Γ σ n) → Acc wt
  wf Γ σ (Var x)                = acc (aux Γ σ (Var x))
  wf Γ σ (wt ⟨ wt₁ ⟩)           = acc (aux Γ σ (wt ⟨ wt₁ ⟩))
  wf Γ .(σ => τ) (Lam σ {τ} wt) = acc (aux Γ (σ => τ) (Lam σ wt))
  wf Γ .(O x) (Lit {.Γ} {x} x₁) = acc (aux Γ (O x) (Lit x₁))



finally : ∀{Γ σ n} → (wt : WT Γ σ n) → TAcc wt
finally wt = allTsAcc wt (wf _ _ wt)

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
