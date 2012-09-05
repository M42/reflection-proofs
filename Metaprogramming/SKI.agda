open import Metaprogramming.Util.Equal
open import Metaprogramming.Util.ConcreteSKI
open import Metaprogramming.Util.Apply

open import Reflection
open import Data.Maybe

module Metaprogramming.SKI (U : Set)
           (equal? : (x : U) → (y : U) → Equal? x y)
           (type? : Name → Maybe U)
           (Uel : U → Set)
           (quoteVal : (x : U) → Term → Uel x)
           (quoteBack : (x : U) → Uel x → Term) where

open import Data.Nat
open import Data.Empty
open import Data.Product hiding (map)
open import Data.Unit hiding (_≤_; _≤?_)
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding (_+_ ; _<_; _≤_ ; suc ; zero) renaming (compare to fcompare)
open import Data.List

import Metaprogramming.Datatypes
open module DT = Metaprogramming.Datatypes U equal? Uel
import Metaprogramming.TypeCheck
open module TC = Metaprogramming.TypeCheck U equal? type? Uel quoteVal quoteBack

-- the Comb datatype represents typed SKI-combinator terms.
-- terms of this structure have sensible types by construction;
-- note how the application constructor matches the function and
-- argument types. The environments are necessary to ensure that
-- closed terms stay closed.
data Comb : (Γ : Ctx) → U' → Set where
  Var    : forall {Γ}        → (τ : U') → τ ∈ Γ → Comb Γ τ
  _⟨_⟩   : forall {Γ σ τ}    → Comb Γ (σ => τ) → Comb Γ σ → Comb Γ τ
  S      : forall {Γ A B C}  → Comb Γ ((A => B => C) => (A => B) => A => C)
  K      : forall {Γ A B}    → Comb Γ (A => B => A)
  I      : forall {Γ A}      → Comb Γ (A => A)
  Lit    : forall {Γ} {x} → Uel x → Comb Γ (O x) -- a constant

-- this function essentially is used whenever a lambda abstraction is
-- encountered.  the abstraction is removed, the body is compiled
-- recursively, and this function, called on the result, replaces
-- possible occurences of (Var 0) (which, if placed directly after the
-- lambda which introduced it, constitutes an identity function) with
-- an I-combinator. in other cases the variable is left alone, but
-- it's index is decreased by one, since there is one less lambda
-- abstraction between it and its binding site. in other cases,
-- i.e. if the body isn't a variable, we can safely replace the lambda
-- + body with a K-combinator applied to the body.
lambda : {σ τ : U'}{Γ : Ctx} → (c : Comb (σ ∷ Γ) τ) → (Comb Γ (σ => τ))
lambda {σ}     (Var .σ   here)    = I
lambda {σ} {τ} (Var .τ (there i)) = K ⟨ Var τ i ⟩
lambda  (t ⟨ t₁ ⟩) = let l1 = lambda  t
                         l2 = lambda  t₁
                      in S ⟨ l1 ⟩ ⟨ l2 ⟩
lambda           (Lit l)          = K ⟨ Lit l ⟩ -- we can't do a catch-all pattern here,
                                                -- since we're sneakily removing a type from
                                                -- the context (namely the one corresponding
                                                -- to the lambda we've just eliminated.
lambda           S                = K ⟨ S ⟩
lambda           K                = K ⟨ K ⟩
lambda           I                = K ⟨ I ⟩

-- recursively compile lambda terms. Var and Lit are boring,
-- obviously, application doesn't change (but it's subterms are
-- compiled), only in the lambda-case does anything interesting
-- happen. The body is compiled, the abstraction is removed, and the
-- lambda function sorts out the aftermath. see above.
compile : (Γ : Ctx) → (τ : U') → {n : ℕ} → WT Γ τ n → (Comb Γ τ)
compile Γ (O σ) (Lit x) = Lit x
compile Γ τ (Var  h) = Var τ  h
compile Γ τ (_⟨_⟩ {.Γ}{σ} wt wt₁) = compile Γ (σ => τ) wt ⟨ compile Γ σ wt₁ ⟩
compile Γ (σ => τ) (Lam .σ wt) = lambda (compile ( σ ∷ Γ) τ wt) 
  

-- a "helpful" wrapper which does nothing except show that we
-- can be certain that a closed term (i.e. empty environment)
-- results in a closed SKI combinator.
-- this irrefutably means that no Vars will be present in the
-- output, by construction of the Comb datatype.
topCompile : {τ : U'} {n : ℕ} → Well-typed-closed τ n → Comb [] τ
topCompile (Lit x) = Lit x
topCompile (Var ())
topCompile {τ}(nwt ⟨ nwt₁ ⟩)      = compile [] τ (nwt ⟨ nwt₁ ⟩)
topCompile {.σ => τ}(Lam σ nwt) = compile [] (σ => τ) (Lam σ nwt)

  
-- inspiration : http://code.haskell.org/~dolio/
-- this function slightly rewrites the (admittedly
-- cumbersome) terms produced by `compile`. the correctness
-- is guaranteed by the type signature preservation as well
-- as that one can trivially see that precisely the semantic
-- rules of the combinators are being interpreted, eg. the I
-- combinator should just return its first argument, etc.

reduce₁ : ∀ {Γ τ} → Comb Γ τ → Comb Γ τ
reduce₁ (I ⟨ c₁ ⟩) = reduce₁ c₁
reduce₁ (S ⟨ f ⟩ ⟨ g ⟩ ⟨ x ⟩ ) = reduce₁ f ⟨ reduce₁ x ⟩ ⟨ reduce₁ g ⟨ reduce₁ x ⟩ ⟩ 
reduce₁ (K ⟨ x ⟩ ⟨ y ⟩) = reduce₁ x
reduce₁ (f ⟨ x ⟩ ) = reduce₁ f ⟨ reduce₁ x ⟩
reduce₁ e = e

reduce : ∀ {Γ τ} → ℕ → Comb Γ τ → Comb Γ τ
reduce zero e = e
reduce (suc n) e = reduce n (reduce₁ e)

private

    -- defining a predicate on Comb's, indicating whether they
    -- have any free variables. this is rather superfluous, because
    -- by the definition of the Comb datatype, an empty environment (Γ)
    -- implies a lack of variables.
    noVar : {τ : U'} → {Γ : Ctx} → Comb Γ τ → Set
    noVar (Lit x) = ⊤
    noVar (Var τ  i) = ⊥
    noVar (_⟨_⟩ c c₁) = noVar c × noVar c₁
    noVar S = ⊤
    noVar K = ⊤
    noVar I = ⊤

    -- a small proof that a term advertising to be closed (i.e. having
    -- an empty environment) indeed contains no variable references.
    -- by definition of the Comb datatype, this proof is trivial. Just
    -- here for sceptics, is all.
    closed→closed : {σ : U'} → (x : Comb [] σ) → noVar x
    closed→closed (Lit x) = tt
    closed→closed {σ} (Var .σ ())
    closed→closed (v ⟨ v₁ ⟩) = (closed→closed v) , (closed→closed v₁)
    closed→closed S = tt
    closed→closed K = tt
    closed→closed I = tt

-- abstract representations of the combinators, to be used for unquoting.
-- note that these are also type-safe.
Srep : ∀ {A B C Γ} → WT Γ ((A => B => C) => (A => B) => A => C) _
Srep {A}{B}{C} = Lam (A => B => C) (Lam (A => B) (Lam A
                      ( Var (there (there here)) ⟨ Var here ⟩ ⟨ (Var (there here)) ⟨ (Var here) ⟩ ⟩ )))

Irep : ∀ {A Γ} → WT Γ (A => A) _
Irep {A} = Lam A (Var here)

Krep : ∀ {A B Γ} → WT Γ (A => B => A) _
Krep {A}{B} = Lam A (Lam B (Var (there here)))

-- the size of a combinator once translated back to WT datatype. this
-- is needed because it cannot be inferred in the ski2wt type signature.
combsz : ∀ {Γ σ} → Comb Γ σ → ℕ
combsz {Γ} {σ} (Var .σ x) = 1
combsz (c ⟨ c₁ ⟩) = suc (combsz c + combsz c₁)
combsz S = 10
combsz K = 3
combsz I = 2
combsz (Lit x₁) = 1

-- convert a term in the combinator language back to WT. this
-- is to be done so that the usual unquote for WT can be used.
-- below an unquote for combinator terms is also defined, redundantly,
-- but it does illustrate a more direct way of introducing applications
-- into concrete Agda, as opposed to the lam2term function, which uses
-- the "Apply" function for the same purpose. 
ski2wt : {Γ : Ctx} {σ : U'} → (c : Comb Γ σ) → WT Γ σ (combsz c)
ski2wt {Γ} {σ} (Var .σ h) = Var h
ski2wt (c ⟨ c₁ ⟩)         = ski2wt c ⟨ ski2wt c₁ ⟩
ski2wt S                  = Srep
ski2wt K                  = Krep
ski2wt I                  = Irep
ski2wt (Lit x₁)           = Lit x₁

-- convert a rich combinator term into abstract untyped Agda, ready to
-- be unquoted and used as a real function again.  reuses code from
-- the CPS developments.  Agda normalises before unquoting, so the
-- terms are relatively neat.
ski2term : {σ : U'} → Comb [] σ → Term
ski2term c = lam2term (ski2wt c) 

-- method to retrieve the type of a combinator term; useful when
-- unquoting (one would like to know the type of the resulting term)
ski2type : {σ : U'} → Comb [] σ → Set
ski2type {σ} c = el' σ

