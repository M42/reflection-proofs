open import Equal
open import Apply
open import Reflection
open import Data.Maybe

module CPS (U : Set) (Uel : U → Set) (equal? : (x : U) → (y : U) → Equal? x y) (type? : Name → Maybe U) (quoteBack : (x : U) → Uel x → Term) (ReturnType : U) where

open import Relation.Nullary.Core
open import Data.Bool hiding (T) renaming (_≟_ to _≟Bool_) 
open import Reflection
open import Data.Nat renaming (_≟_ to _≟-Nat_)

open import Data.Stream using (Stream ; evens ; odds ; _∷_ )
open import Coinduction
open import Data.Maybe
open import Data.Empty
open import Data.Product hiding (map)
open import Data.Unit hiding (_≤_; _≤?_)
open import Relation.Binary.PropositionalEquality
open import Data.String renaming (_++_ to _+S+_)
open import Data.Fin hiding (_+_ ; _<_; _≤_ ; suc ; zero) renaming (compare to fcompare)
open import Data.List

import Datatypes
open module DT = Datatypes U equal? Uel
import TypeCheck
open module TC = TypeCheck U equal? type? Uel


map/k : {a b : Set} → (a → (a → b) → b) → List a → (List a → b) → b
map/k f/k []       k = k []
map/k f/k (x ∷ xs) k = f/k x (λ v → (map/k f/k xs (λ v-rest → k (v ∷ v-rest))))



testlist : List ℕ
testlist = 1 ∷ 2 ∷ 3 ∷ []

identity : {a : Set} → a → a
identity x = x

incrlist  : List ℕ
incrlist  = map/k (λ n k → k (suc n)) testlist identity
-- ... as opposed to
incrlist' : List ℕ
incrlist' = map (λ n → suc n) testlist

------------
-- CPS types
------------

-- result type...

RT : U'
RT = O ReturnType

-- the CPS transformation, take 1:

noApp : {σ : U'} {Γ : Ctx} → WT Γ σ → Set
noApp (Var inpf)   = ⊤
noApp (Lam σ wt)   = ⊤
noApp (wt ⟨ wt₁ ⟩) = ⊥
noApp (Lit x )     = ⊥

-- and now the hybrid approach
-- thanks to http://matt.might.net/articles/cps-conversion/

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
weak : forall {Γ' τ Γ} → WT (Γ' ++ Γ) τ → (τ' : U') → WT (Γ' ++ (τ' ∷ Γ)) τ
weak (Lit x) t = Lit x
weak {Γ'} (Var x) t' = Var (weakvar t' Γ' x)
weak {g'} {t => t1} (Lam .t e) t' = Lam t (weak { t ∷ g' } e t')
weak {g'} {t2} {g} (_⟨_⟩ .{_}{t1}.{t2} e1 e2) t' =
               (weak {g'} {t1 => t2} e1 t')
               ⟨   (weak {g'} {t1} e2 t') ⟩
 
-- increase all the de Bruijn indices by 1. Needs to have some
-- arbitrary type added to the front of the environment to keep
-- the lengths right. special case of weakening, but with empty prefix environment.
shift1 : forall {Γ τ} → (τ' : U') → WT Γ τ → WT (τ' ∷ Γ) τ
shift1 t' e = weak {[]} e t'



data TAcc : {Γ : Ctx} {σ : U'} → WT Γ σ → Set where
  TBaseLit : forall {Γ σ x} → TAcc (Lit {Γ} {σ} x)
  TBaseVar : forall {Γ σ x} → TAcc (Var {Γ} {σ} x)
  TLam : forall {Γ t1 t2} {a : WT (t1 ∷ Γ) t2}
         → TAcc (shift1 (Cont t2) a)
         → TAcc {Γ} {t1 => t2} (Lam {Γ} t1 a)
  TApp : forall {Γ σ σ₁} {a : WT Γ (σ => σ₁)} {b : WT Γ σ}
         → TAcc {Γ} {σ => σ₁} a
         → TAcc (shift1 (σ => σ₁) b)
         → TAcc (a ⟨ b ⟩)



-- M converts a lambda or a var into an atomic CPS expression
-- M has been inlined into the Var and Lam cases in T

-- T takes an expression and a syntactic continuation, and applies the
--   continuation to a CPS-converted version of the expression.
T : {σ : U'} {Γ : Ctx} → (wt : WT Γ σ) → TAcc wt → WT (map cpsType Γ) (cpsType σ => RT) → WT (map cpsType Γ) RT
T (Lit x)             TBaseLit                    cont = cont ⟨ (Lit x) ⟩
T (Var inpf  )        TBaseVar                    cont = cont ⟨ (Var (cpsvar inpf)) ⟩
T {t1 => t2} {Γ} (Lam .t1 expr)     (TLam pf)     cont = cont ⟨ (Lam (cpsType t1) (Lam (cpsType t2 => RT) (T (shift1 (Cont t2) expr) pf (Var here)))) ⟩
T .{σ₂} {Γ} (_⟨_⟩ .{_}{σ₁}{σ₂} f e)  (TApp pf pf2) cont =
   T f pf (Lam (cpsType σ₁ => ((cpsType σ₂ => RT) => RT))
                           (T (shift1 (σ₁ => σ₂) e) pf2 (Lam (cpsType σ₁)
                              (((Var (there here)) ⟨ (Var here) ⟩ ) 
                                  ⟨ (shift1 (cpsType σ₁) (shift1 (cpsType σ₁ => ((cpsType σ₂ => RT) => RT)) cont)) ⟩ ))))



-- id1 : forall {x} → WT [] (O x => O x)
-- id1 {x} = Lam (O x) (Var here)
-- id2 : forall {x} → WT (O x => O  x ∷ []) ((O x => O x) => (O x => O x))
-- id2 {x} = Lam (O x => O x) (Var (there here))




























-- mutual
--   T-c : forall {σ Γ} → WT Γ σ → WT (map cpsType Γ) (cpsType σ => RT) → WT (map cpsType Γ) RT
--   T-c (Halt t)    c = {!!}
--   T-c (Var inpf ) c = App c (M-h (Var inpf) tt)
--   T-c (Lam σ t  ) c = App c (M-h (Lam σ t)  tt)
--   T-c (App f e  ) c = T-k f (λ $f →
--                                   T-k e (λ $e →
--                                       App (App {!!} $e) c))
-- 
--   T-k : forall {σ Γ} → WT Γ σ
--                      → (WT (map cpsType Γ) (cpsType σ) → WT (map cpsType Γ) RT)
--                      → WT (map cpsType Γ) RT
--   T-k (Halt t)    k = {!!}
--   T-k (Var inpf ) k = k (M-h (Var inpf) tt)
--   T-k (Lam σ t  ) k = k (M-h (Lam σ t) tt)
--   T-k {σ} {Γ} (App f e  ) k = 
--                          T-k f ( (λ $f →
--                                T-k e ((λ $e →
--                                    App (App  $f  $e) cont ))))
--        where
--            cont : WT (map cpsType Γ) (cpsType σ => RT)
--            cont = Lam (cpsType σ)
--                               (k ((Var {{!!}} {!here {?} {?}!})) ) -- Lam ($rv ∷ []) (k (Var $rv))
-- 
--   M-h : {σ : U'} {Γ : Ctx} → (t : WT Γ σ) → noApp t → WT (map cpsType Γ) (cpsType σ)
--   M-h {t1 => t2} (Lam .t1 t) pf = Lam (cpsType t1)
--                                       (Lam (cpsType t2 => RT)
--                                            (T-c (shift1 (Cont t2) t) (Var here)))
--   M-h (Var inpf) pf = Var (cpsvar inpf)
--   M-h (App t t₁) ()
--   M-h (Halt t )  ()

-- testIdId = T-c id1 id2
