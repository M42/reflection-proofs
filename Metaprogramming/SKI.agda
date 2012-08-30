open import Equal
open import Reflection
open import Data.Maybe

module SKI (U : Set)
           (equal? : (x : U) → (y : U) → Equal? x y)
           (type? : Name → Maybe U)
           (Uel : U → Set)
           (quoteVal : (x : U) → Term → Uel x)
           (quoteBack : (x : U) → Uel x → Term) where

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
open module TC = TypeCheck U equal? type? Uel quoteVal quoteBack

module SKI where

open import Data.Nat

NamedCtx : Set
NamedCtx = List (ℕ × U')


-- inspiration : http://code.haskell.org/~dolio/

-- new idea: give Comb a notion of environments.

data Comb : (Γ : NamedCtx) → U' → Set where
  Var    : forall {Γ}        → (τ : U') → (n : ℕ) → (n , τ) ∈ Γ → Comb Γ τ
  _⟨_⟩   : forall {Γ σ τ}    → Comb Γ (σ => τ) → Comb Γ σ → Comb Γ τ
  S      : forall {Γ A B C}  → Comb Γ ((A => B => C) => (A => B) => A => C)
  K      : forall {Γ A B}    → Comb Γ (A => B => A)
  I      : forall {Γ A}      → Comb Γ (A => A)
  Lit    : forall {Γ} {x} → Uel x → Comb Γ (O x) -- a constant



lambda : {σ τ : U'}{Γ : NamedCtx} → (n : ℕ) → (c : Comb ((n , σ) ∷ Γ) τ) → (Comb Γ (σ => τ))
lambda          x (Lit l)    = K ⟨ Lit l ⟩
lambda          x S          = K ⟨ S ⟩
lambda          x K          = K ⟨ K ⟩
lambda          x I          = K ⟨ I ⟩
lambda {σ} x (Var .σ .x here) = I
lambda {σ} {τ} x (Var .τ n (there i)) = K ⟨ Var τ n i ⟩
lambda x (t ⟨ t₁ ⟩) = let l1 = lambda x t
                          l2 = lambda x t₁
                      in S ⟨ l1 ⟩ ⟨ l2 ⟩

data NamedWT : (Γ : NamedCtx) → U' → ℕ → Set where
  Var   : forall {Γ} {τ} → (n : ℕ)  → (n , τ) ∈ Γ → NamedWT Γ τ 1
  _⟨_⟩  : forall {Γ} {σ τ} {n m} → NamedWT Γ (σ => τ) n → NamedWT Γ σ m → NamedWT Γ τ (suc n + m)
  Lam   : forall {Γ} {τ} {n} → (x : ℕ) → (σ : U') → NamedWT ((x , σ) ∷ Γ) τ n → NamedWT Γ (σ => τ) (suc n)
  Lit   : forall {Γ} {x} → Uel x → NamedWT Γ (O x) 1 -- a constant

compile : (Γ : NamedCtx) → (τ : U') → {n : ℕ} → NamedWT Γ τ n → (Comb Γ τ)
compile Γ (O σ) (Lit x) = Lit x
compile Γ τ (Var n h) = Var τ n h
compile Γ τ (_⟨_⟩ {.Γ}{σ} wt wt₁) = compile Γ (σ => τ) wt ⟨ compile Γ σ wt₁ ⟩
compile Γ (σ => τ) (Lam x .σ wt) = lambda x (compile ((x , σ) ∷ Γ) τ wt) 
  
topCompile : {τ : U'} {n : ℕ} → NamedWT [] τ n → Comb [] τ
topCompile (Lit x) = Lit x
topCompile (Var n ())
topCompile {τ}(nwt ⟨ nwt₁ ⟩)      = compile [] τ (nwt ⟨ nwt₁ ⟩)
topCompile {.σ => τ}(Lam x σ nwt) = compile [] (σ => τ) (Lam x σ nwt)

  
open import Data.Vec hiding (_∈_)

Substitution : ℕ → Set
Substitution n = Vec ℕ n

sub : (c : Ctx) → Substitution (length c) → NamedCtx
sub [] [] = []
sub (x ∷ subs) (x₁ ∷ ctx) = (x₁ , x) ∷ sub subs ctx


coerce∈ : forall {τ} → (Γ : Ctx) → (s : Substitution (length Γ)) → (idx : τ ∈ Γ) → (lookup (finindex idx) s , τ) ∈ sub Γ s
coerce∈ {τ} .(τ ∷ []) sub (here {[]}) with sub
coerce∈ {τ} .(τ ∷ []) sub (here {[]}) | x ∷ [] = here -- force Agda to notice sub is 1 long.
coerce∈ {τ} .(τ ∷ x ∷ xs) sub (here {x ∷ xs}) with sub
coerce∈ {τ} .(τ ∷ xs ∷ sub) xs (here {sub ∷ x₁}) | x ∷ x₂ ∷ a = here -- same story, but sub has length of Γ
coerce∈ .(y ∷ xs) sub (there {xs} {y} idx) with sub
coerce∈ .(y ∷ xs) xs (there {y} idx) | x ∷ a = there (coerce∈ y a idx)

unbrown' : forall {σ n} → (Γ : Ctx) → FreshVariables → (s : Substitution (length Γ)) → WT Γ σ n → NamedWT (sub Γ s) σ n
unbrown' Γ (f ∷ fs) sub (Var x)      = Var (lookup (finindex x) sub) (coerce∈ Γ sub x)
unbrown' Γ (f ∷ fs) sub (wt ⟨ wt₁ ⟩) = unbrown' Γ (evens (♭ fs)) sub wt ⟨ unbrown' Γ (odds (♭ fs)) sub wt₁ ⟩
unbrown' Γ (f ∷ fs) sub (Lam σ wt)   = Lam f σ (unbrown' (σ ∷ Γ) (♭ fs) (f ∷ sub) wt)
unbrown' Γ (f ∷ fs) sub (Lit x)      = Lit x

unbrown : {σ : U'} {n : ℕ} → WT [] σ n → NamedWT [] σ n
unbrown = unbrown' [] fv []

flatten : NamedCtx → Ctx
flatten [] = []
flatten ((n , σ) ∷ xs) = σ ∷ flatten xs

coerce∋ : forall {n τ} → (Γ : NamedCtx) → (idx : (n , τ) ∈ Γ) → (τ ∈ flatten Γ)
coerce∋ {n} {τ} .((n , τ) ∷ xs) (here {xs}) = here
coerce∋ .(y ∷ xs) (there {xs} {y} idx)      = there (coerce∋ xs idx)

brown : forall {σ n} → (Γ : NamedCtx) → NamedWT Γ σ n → WT (flatten Γ) σ n
brown Γ (Lit x)      = Lit x
brown Γ (Var n x)    = Var (coerce∋ Γ x)
brown Γ (wt ⟨ wt₁ ⟩) = (brown Γ wt) ⟨ brown Γ wt₁ ⟩
brown Γ (Lam x σ wt) = Lam σ (brown ((x , σ) ∷ Γ) wt)

private

    noVar : {τ : U'} → {Γ : NamedCtx} → Comb Γ τ → Set
    noVar (Lit x) = ⊤
    noVar (Var τ x i) = ⊥
    noVar (_⟨_⟩ c c₁) = noVar c × noVar c₁
    noVar S = ⊤
    noVar K = ⊤
    noVar I = ⊤

    closed→closed : {σ : U'} → (x : Comb [] σ) → noVar x
    closed→closed (Lit x) = tt
    closed→closed {σ} (Var .σ n ())
    closed→closed (v ⟨ v₁ ⟩) = (closed→closed v) , (closed→closed v₁)
    closed→closed S = tt
    closed→closed K = tt
    closed→closed I = tt


Srep : ∀ {A B C Γ} → WT Γ ((A => B => C) => (A => B) => A => C) _
Srep {A}{B}{C} = Lam (A => B => C) (Lam (A => B) (Lam A
                      ( Var (there (there here)) ⟨ Var here ⟩ ⟨ (Var (there here)) ⟨ (Var here) ⟩ ⟩ )))

Irep : ∀ {A Γ} → WT Γ (A => A) _
Irep {A} = Lam A (Var here)

Krep : ∀ {A B Γ} → WT Γ (A => B => A) _
Krep {A}{B} = Lam A (Lam B (Var (there here)))

combsz : ∀ {Γ σ} → Comb Γ σ → ℕ
combsz {Γ} {σ} (Var .σ n x) = 1
combsz (c ⟨ c₁ ⟩) = suc (combsz c + combsz c₁)
combsz S = 10
combsz K = 3
combsz I = 2
combsz (Lit x₁) = 1

ski2wt : {Γ : NamedCtx} {σ : U'} → (c : Comb Γ σ) → WT (flatten Γ) σ (combsz c)
ski2wt {Γ} {σ} (Var .σ n h) = Var (coerce∋ Γ h)
ski2wt (c ⟨ c₁ ⟩) = ski2wt c ⟨ ski2wt c₁ ⟩
ski2wt S = Srep
ski2wt K = Krep
ski2wt I = Irep
ski2wt (Lit x₁) = Lit x₁

open import ConcreteSKI
open import Apply

ski2term : {σ : U'} → Comb [] σ → Term
ski2term {O σ} (Lit x) = quoteBack σ x
ski2term {σ} (Var .σ n ())
ski2term (c ⟨ c₁ ⟩) = lam visible pleaseinfer (lam visible pleaseinfer (var 1 (arg visible relevant (var 0 []) ∷ [])))
ski2term {(a => b => c) => (.a => .b) => .a => .c} S =      lam visible pleaseinfer (
                                                               lam visible pleaseinfer (
                                                                  lam visible pleaseinfer (def (quote s) (
                                                                       arg visible relevant (var 2 []) ∷
                                                                       arg visible relevant (var 1 []) ∷
                                                                       arg visible relevant (var 0 []) ∷ []))))
ski2term {a => b => .a} K   = lam visible pleaseinfer (
                                 lam visible pleaseinfer (def (quote k) (
                                     arg visible relevant (var 1 []) ∷
                                     arg visible relevant (var 0 []) ∷ [])))
ski2term {a => .a} I        = lam visible pleaseinfer (def (quote i) (
                                 arg visible relevant (var 0 []) ∷ []))

ski2type : {σ : U'} → Comb [] σ → Set
ski2type {σ} c = el' σ

-- alternative; this is shorter.
ski2term' : {σ : U'} → Comb [] σ → Term
ski2term' c = lam2term (ski2wt c) 

