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

-- type signatures. Either a base type or a function, and then continuations.
data U' : Set where
  O    : U → U'
  _=>_ : U' → U' → U'
  Cont : U' → U'

-- casting our universe back to real Agda. We use the argument Uel
-- to the module to cast type variables living in U to Set. The user
-- should provide this.
el' : U' → Set
el' (O x) = Uel x
el' (u => u₁) = el' u → el' u₁
el' (Cont t) = ⊥ -- arbitrary, as `el' (Cont _)` is never called.

-- decidable equality on types. if we encounter an O x, we need
-- to ask the user if the types are equal.
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
-- that they're lambdas. this is what we'll initially
-- quote lambda's to, before inferring types.
data Raw : Set where
  Var  : ℕ              → Raw
  App  : Raw   → Raw    → Raw
  Lam  : U'    → Raw    → Raw
  Lit  : (x : U)   →  Uel x → Raw

-----------------------------------------------------------------------------
-- Well-scoped, well-typed lambda terms
-----------------------------------------------------------------------------

-- a list of types constitutes a context
Ctx : Set
Ctx = List U'

infix 3 _∈_
-- this is a way of showing that a value is present in a list.
-- it doubles as an index (de Bruijn) too. 
data _∈_ {A : Set} (x : A) : List A → Set where
  here    : {xs : List A} → x ∈ x ∷ xs
  there   : {xs : List A} {y : A} → x ∈ xs → x ∈ y ∷ xs

-- terms of type WT are, by construction, both well-typed (see the
-- type arguments which have to "fit" sensibly) and well-scoped
-- (notice the _∈_ used to force variables to point to some type
-- in the type context Γ).
data WT : Ctx → U' → ℕ → Set where
  Var   : ∀ {Γ} {τ}      → τ ∈ Γ → WT Γ τ 1
  _⟨_⟩  : ∀ {Γ} {σ τ} {n m}   → WT Γ (σ => τ) n → WT Γ σ m → WT Γ τ (suc n + m)
  Lam   : ∀ {Γ} σ {τ} {n}   → WT (σ ∷ Γ) τ n → WT Γ (σ => τ) (suc n)
  Lit   : ∀ {Γ} {x}      → Uel x → WT Γ (O x) 1 -- a constant
  
Well-typed-closed : U' → ℕ → Set
Well-typed-closed = WT []

-- an ugly little hack to make WT terms homogeneous (and thus
-- comparable, for purposes of well-foundedness), even if they differ
-- in type, context or size.
WTpack = Σ ℕ (λ n → Σ U' (λ u → Σ Ctx (λ g → WT g u n)))

-- helper functions to extract the type parameters for WT from a WTpack value.
getEnv : WTpack → Ctx
getEnv (proj₁ , proj₂ , proj₃ , proj₄) = proj₃
getType : WTpack → U'
getType (proj₁ , proj₂ , proj₃ , proj₄) = proj₂
sz : WTpack → ℕ
sz (proj₁ , proj₂ , proj₃ , proj₄) = proj₁

-- embedding into WTpack. pretty trivial.
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

  -- we would like to build a value of type Iso WTpack (WT _ _ _) but
  -- cannot, for the same reason we could not prove well-foundedness
  -- using WT types directly. The user will just have to believe us on
  -- this one, since we have the to, from, tofrom, fromto proofs lying
  -- around separately.

wtSize : ∀{Γ σ n} → WT Γ σ n → ℕ
wtSize {_}{_}{n} wt = n

-- give the position of an _∈_ value in a list.
index : {A : Set} {x : A} {xs : List A} → x ∈ xs → ℕ
index   here    = zero
index (there h) = suc (index h)
-- or, optionally, return a Fin.
finindex : {A : Set} {x : A} {xs : List A} → x ∈ xs → Fin (length xs)
finindex   here     = zero
finindex (there h)  = suc (finindex h)

-- a view on lists
data Lookup {A : Set} (xs : List A) : ℕ → Set where
  inside   : (x : A) (p : x ∈ xs) → Lookup xs (index p)
  outside  : (m : ℕ) → Lookup xs (length xs + m)

-- a lookup function returning the Lookup view.
_!_ : {A : Set} (xs : List A) (n : ℕ) → Lookup xs n
[]        ! n      = outside n
(x ∷ x₁)  ! zero   = inside x here
(x ∷ x₁)  ! suc n with x₁ ! n
(x₂ ∷ x₁) ! suc .(index p)       | inside x p  = inside x (there p)
(x ∷ x₁)  ! suc .(length x₁ + m) | outside  m  = outside m

-- the way to get untyped terms back (`forget`, as it were)
erase : ∀ {Γ τ n} → WT Γ τ n → Raw
erase (Var inpf)      = Var (index inpf)
erase (t ⟨ t₁ ⟩)      = App (erase t) (erase t₁)
erase (Lam σ t)       = Lam σ (erase t)
erase (Lit {_}{σ} x)  = Lit σ x

-- yet another view, this time on Raw terms. if we can manage
-- to infer a type, we give it along with the corresponding WT term.
-- WT and Raw aren't isomorphic, since Raw can also represent nonsensical
-- terms such as App (Var 0) (Var 0) without any context (one may only introduce
-- variables inside abstractions, otherwise scoping breaks).
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
    
-- a predicate reflecting that some natural is smaller than some other natural
data _<_ (m : ℕ) : ℕ → Set where
  <-base : m < suc m
  <-step : {n : ℕ} → m < n → m < suc n

