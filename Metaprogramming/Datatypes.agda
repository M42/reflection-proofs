open import Metaprogramming.Util.Equal

module Metaprogramming.Datatypes (U : Set) (equal? : (x : U) → (y : U) → Equal? x y) (Uel : U → Set) where

open import Data.List
open import Data.Nat hiding (_≟_ ; _<_)
open import Data.Unit hiding (_≟_)
open import Data.Empty
open import Data.Product
open import Data.Fin using (Fin ;  zero ; suc)
open import Relation.Binary.PropositionalEquality

infixl 30 _⟨_⟩ 
infixr 20 _=>_

-- type signatures. Either a base type or a function. and then continuations.
data U' : Set where
  O    : U → U'
  _=>_ : U' → U' → U'
  Cont : U' → U'

el' : U' -> Set
el' (O x) = Uel x
el' (u => u₁) = el' u → el' u₁
el' (Cont t) = ⊥ -- arbitrary, as `el' (Cont _)` is never called.

_=?=_ : (σ τ : U') → Equal? σ τ
O x          =?= O  y       with (equal? x y)
O .y         =?= O y  | yes = yes
O x          =?= O y  | no  = no
O x          =?= (_ => _)   = no
(σ => τ)     =?= O  y       = no
(σ₁ => τ₁)   =?= (σ₂ => τ₂) with σ₁ =?= σ₂ | τ₁ =?= τ₂
(.σ₂ => .τ₂) =?= (σ₂ => τ₂) | yes | yes = yes
(.σ₂ => τ₁)  =?= (σ₂ => τ₂) | yes | no  = no
(σ₁ => .τ₂)  =?= (σ₂ => τ₂) | no  | yes = no
(σ₁ => τ₁)   =?= (σ₂ => τ₂) | no  | no  = no
O x          =?= Cont b     = no
(a => a₁)    =?= Cont b     = no
Cont a       =?= O y        = no
Cont a       =?= (b => b₁)  = no
Cont a       =?= Cont b     with a =?= b
Cont .b      =?= Cont b     | yes = yes
Cont a       =?= Cont b     | no  = no

-- we don't know anything about Raws, except
-- that they're lambdas.
data Raw : Set where
  Var  : ℕ              → Raw
  App  : Raw   → Raw    → Raw
  Lam  : U'    → Raw    → Raw
  Lit  : (x : U)   →  Uel x → Raw

open import Data.Stream using (Stream ; _∷_)
open import Coinduction

-----------------------------------------------------------------------------
-- Well-scoped, well-typed lambda terms
-----------------------------------------------------------------------------

-- this will probably become a Vec later.
Ctx : Set
Ctx = List U'

infix 3 _∈_

data _∈_ {A : Set} (x : A) : List A → Set where
  here    : {xs : List A} → x ∈ x ∷ xs
  there   : {xs : List A} {y : A} → x ∈ xs → x ∈ y ∷ xs
  
data WT : (Γ : Ctx) → U' → ℕ → Set where
  Var   : forall {Γ} {τ}      → τ ∈ Γ → WT Γ τ 1
  _⟨_⟩  : forall {Γ} {σ τ} {n m}   → WT Γ (σ => τ) n → WT Γ σ m → WT Γ τ (suc n + m)
  Lam   : forall {Γ} σ {τ} {n}   → WT (σ ∷ Γ) τ n → WT Γ (σ => τ) (suc n)
  Lit   : forall {Γ} {x}      → Uel x → WT Γ (O x) 1 -- a constant

WTpack = Σ ℕ (λ n → Σ U' (λ u → Σ Ctx (λ g → WT g u n)))

getEnv : WTpack → Ctx
getEnv (proj₁ , proj₂ , proj₃ , proj₄) = proj₃
getType : WTpack → U'
getType (proj₁ , proj₂ , proj₃ , proj₄) = proj₂
sz : WTpack → ℕ
sz (proj₁ , proj₂ , proj₃ , proj₄) = proj₁

to : ∀ {Γ σ n} → WT Γ σ n → WTpack
to {Γ}{σ}{n} wt = n , σ , Γ , wt

private
  -- showing that we have a valid isomorphism between
  -- WT and WTpack
  fromWT : (p : WTpack) → WT (getEnv p) (getType p) (sz p)
  fromWT (p1 , p2 , p3 , p4 ) = p4
  
  from-toWT : ∀ {Γ σ n} → {x : WT Γ σ n} → fromWT (to x) ≡ x
  from-toWT = refl
  
  to-fromWT : ∀ {x : WTpack} → to (fromWT x) ≡ x
  to-fromWT = refl


wtSize : ∀{Γ σ n} → WT Γ σ n → ℕ
wtSize {_}{_}{n} wt = n

index : {A : Set} {x : A} {xs : List A} → x ∈ xs → ℕ
index   here    = zero
index (there h) = suc (index h)

-- or, optionally, return a Fin.
finindex : {A : Set} {x : A} {xs : List A} → x ∈ xs → Fin (length xs)
finindex   here     = zero
finindex (there h)  = suc (finindex h)

data Lookup {A : Set} (xs : List A) : ℕ → Set where
  inside   : (x : A) (p : x ∈ xs) → Lookup xs (index p)
  outside  : (m : ℕ) → Lookup xs (length xs + m)

_!_ : {A : Set} (xs : List A) (n : ℕ) → Lookup xs n
[]        ! n      = outside n
(x ∷ x₁)  ! zero   = inside x here
(x ∷ x₁)  ! suc n with x₁ ! n
(x₂ ∷ x₁) ! suc .(index p)       | inside x p  = inside x (there p)
(x ∷ x₁)  ! suc .(length x₁ + m) | outside  m  = outside m

-- the way to get untyped terms back
erase : forall {Γ τ n} → WT Γ τ n → Raw
erase (Var inpf)      = Var (index inpf)
erase (t ⟨ t₁ ⟩)      = App (erase t) (erase t₁)
erase (Lam σ t)       = Lam σ (erase t)
erase (Lit {_}{σ} x)  = Lit σ x

data Infer (Γ : Ctx) : Raw → Set where
  ok    : (n : ℕ)(τ : U') (t : WT Γ τ n)  → Infer Γ (erase t)
  bad   : {e : Raw}              → Infer Γ e

-- We capture that two sets are isomorphic using the following record.
record Iso (A B : Set) : Set where
  field
    from    : A → B
    isoto   : B → A
    from-to : {x : B} → from (isoto x) ≡ x
    to-from : {x : A} → isoto (from x) ≡ x
    
data _<_ (m : ℕ) : ℕ → Set where
  <-base : m < suc m
  <-step : {n : ℕ} → m < n → m < suc n

