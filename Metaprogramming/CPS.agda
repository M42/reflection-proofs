open import Metaprogramming.Util.Equal
open import Metaprogramming.Util.Apply
open import Reflection
open import Data.Maybe

module Metaprogramming.CPS (U : Set)
           (Uel : U → Set)
           (equal? : (x : U) → (y : U) → Equal? x y)
           (type? : Name → Maybe U)
           (quoteBack : (x : U) → Uel x → Term)
           (ReturnType : U) where

open import Data.Bool hiding (T) renaming (_≟_ to _≟Bool_) 
open import Reflection
open import Data.Nat  hiding (_<_) renaming (_≟_ to _≟-Nat_)
open import Relation.Binary
open import Data.Stream using (Stream ; evens ; odds ; _∷_ )
open import Coinduction
open import Data.Maybe
open import Data.Empty
open import Data.Product hiding (map)
open import Data.Unit hiding (_≤_; _≤?_)
open import Data.Fin hiding (_≺_ ; _+_ ; _<_; _≤_ ; suc ; zero) renaming (compare to fcompare)
open import Data.List

import Metaprogramming.Datatypes
open module DT = Metaprogramming.Datatypes U equal? Uel
import Metaprogramming.TypeCheck
open module TC = Metaprogramming.TypeCheck U equal? type? Uel


-- result type...
RT : U'
RT = O ReturnType

noApp : {σ : U'} {Γ : Ctx} {n : ℕ} → WT Γ σ n → Set
noApp (Var inpf)   = ⊤
noApp (Lam σ wt)   = ⊤
noApp (wt ⟨ wt₁ ⟩) = ⊥
noApp (Lit x )     = ⊥

cpsType : U' → U'
cpsType (O x)     = O x
cpsType (t => t₁) = cpsType t => ((cpsType t₁ => RT) => RT)
cpsType (Cont t)  = cpsType t => RT

cpsvar : forall {t g} → t ∈ g → (cpsType t) ∈ (map cpsType g)
cpsvar   here    = here
cpsvar (there v) = there (cpsvar v)

-- show that we can add more variables to our environment for free;
-- variables that used to be in the environment are still there 
weakvar : forall {τ Γ} → (τ' : U') → (Γ' : Ctx) → τ ∈ (Γ' ++ Γ) → τ ∈ (Γ' ++ (τ' ∷ Γ))
weakvar t' [] x = there x
weakvar t' (x ∷ env) here = here
weakvar t' (x ∷ env) (there x₁) = there (weakvar t' env x₁)


-- show that we can add a type variable somewhere in the middle of our
-- environment and stuff still is okay.
weak : forall {Γ' τ Γ n} → WT (Γ' ++ Γ) τ n → (τ' : U') → WT (Γ' ++ (τ' ∷ Γ)) τ n
weak (Lit x) t = Lit x
weak {Γ'} (Var x) t' = Var (weakvar t' Γ' x)
weak {g'} {t => t1} (Lam .t e) t' = Lam t (weak { t ∷ g' } e t')
weak {g'} {t2} {g} (_⟨_⟩ .{_}{t1}.{t2} e1 e2) t' =
               (weak {g'} {t1 => t2} e1 t')
               ⟨   (weak {g'} {t1} e2 t') ⟩
 
-- increase all the de Bruijn indices by 1. Needs to have some
-- arbitrary type added to the front of the environment to keep
-- the lengths right. special case of weakening, but with empty prefix environment.
shift1 : forall {Γ τ n} → (τ' : U') → WT Γ τ n → WT (τ' ∷ Γ) τ n
shift1 t' e = weak {[]} e t'

data TAcc : {Γ : Ctx} {σ : U'} {n : ℕ} → WT Γ σ n → Set where
  TBaseLit : forall {Γ σ x} → TAcc (Lit {Γ} {σ} x)
  TBaseVar : forall {Γ σ x} → TAcc (Var {Γ} {σ} x)
  TLam : forall {Γ t1 t2 n} {a : WT (t1 ∷ Γ) t2 n}
         → TAcc (shift1 (Cont t2) a)
         → TAcc {Γ} {t1 => t2}{suc n} (Lam {Γ} t1 a)
  TApp : forall {Γ σ σ₁ sza szb} {a : WT Γ (σ => σ₁) sza} {b : WT Γ σ szb}
         → TAcc {Γ} {σ => σ₁}{sza} a
         → TAcc {_}{_}{szb}(shift1 (σ => σ₁) b)
         → TAcc {_}{_}{suc sza + szb} (_⟨_⟩ {_}{_}{_}{sza}{szb} a b)

sizeCPS : {σ : U'} {Γ : Ctx} {n : ℕ} → (wt : WT Γ σ n) → (TAcc wt) → (m : ℕ) → ℕ
sizeCPS wt acc cont with wtSize wt
... | a with wt
sizeCPS wt acc cont | .1 | Var x = suc cont + 1
sizeCPS {σ₂} wt (TApp pf pf2) cont | .(suc (n + m)) | _⟨_⟩ {._} {σ₁} {.σ₂} {n} {m} f e = sizeCPS f pf (suc (sizeCPS (shift1 (σ₁ => σ₂) e) pf2 (suc (suc 3 + cont))))
sizeCPS {t1 => t2} wt (TLam pf) cont | .(suc n) | Lam .t1 {.t2} {n} z = suc (cont + suc (suc (sizeCPS (shift1 (Cont t2) z) pf 1)))
sizeCPS wt acc cont | .1 | Lit x₁ = suc cont + 1


-- T takes an expression and a syntactic continuation, and applies the
--   continuation to a CPS-converted version of the expression.
T' : {σ : U'} {Γ : Ctx} {n m : ℕ} → (wt : WT Γ σ n) → (ta : TAcc wt) → (cont : WT (map cpsType Γ) (cpsType σ => RT) m) → WT (map cpsType Γ) RT (sizeCPS wt ta m)
T' {O σ}{Γ} .(Lit x) (TBaseLit {.Γ} {.σ} {x}) cont = cont ⟨ Lit x ⟩
T' {σ}{Γ} .(Var x) (TBaseVar {.Γ} {.σ} {x}) cont = cont ⟨ Var (cpsvar x) ⟩
T' {t1 => t2} {Γ}{suc n}{m} (Lam .t1 expr)     (TLam pf)     cont = cont ⟨ (Lam (cpsType t1) (Lam (cpsType t2 => RT) (T' (shift1 (Cont t2) expr) pf (Var here)))) ⟩
T' .{σ₂} {Γ} (_⟨_⟩ .{_}{σ₁}{σ₂}{n}{m} f e)  (TApp pf pf2) cont =
  T' f pf (Lam (cpsType σ₁ => (cpsType σ₂ => RT) => RT)
                           (T' (shift1 (σ₁ => σ₂) e) pf2 (Lam (cpsType σ₁)
                              ((Var (there here)) ⟨ Var here ⟩  
                                  ⟨ shift1 (cpsType σ₁) (shift1 (cpsType σ₁ => (cpsType σ₂ => RT) => RT) cont) ⟩ ))))
                                  
import Metaprogramming.WTWellfounded
open module WTWf = Metaprogramming.WTWellfounded U equal? Uel type? quoteBack ReturnType
open import Induction.WellFounded

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

private
  allTsAcc : forall {Γ σ n} → (wt : WT Γ σ n) → Acc _≺_ (to wt) → TAcc wt
  allTsAcc (Var x) _ = TBaseVar
  allTsAcc (Lit x₁) _ = TBaseLit
  allTsAcc {Γ} {τ => σ}{suc n} (Lam .τ wt) (acc x) = TLam (allTsAcc (shift1 (Cont σ) wt) (x (to (shift1 (Cont σ) wt)) <-base))
  allTsAcc (_⟨_⟩ {Γ}{σ}{σ₁}{n}{m} wt wt₁) (acc x) = TApp (allTsAcc wt (x (to wt) triv))
                                                         (allTsAcc (shift1 (σ => σ₁) wt₁) (x (to (shift1 (σ => σ₁) wt₁)) (triv2 {_}{n})) )

T : {σ : U'} {Γ : Ctx} {n m : ℕ} → (wt : WT Γ σ n)
                                 → (cont : WT (map cpsType Γ) (cpsType σ => RT) m)
                                 → WT (map cpsType Γ) RT (sizeCPS wt (allTsAcc wt (wf (to wt))) m)
T wt cont = T' wt (allTsAcc wt (wf (to wt))) cont
