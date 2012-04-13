module Bool where

open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Data.Bool

¬_ : Bool → Bool
¬_ = not

-- here's something the type system gives us
-- for free: (i.e. not not true is evaluated,
-- then refl works)
-- this works because the type system does beta-reduction.
trueisnotnottrue : true ≡ ¬ ( ¬ true)
trueisnotnottrue = refl

-- eventually we'd like to prove these kinds of tautologies:
myfavouritetheorem : Set
myfavouritetheorem = {p1 q1 p2 q2 : Bool} → (p1 ∨ q1) ∧ (p2 ∨ q2) ≡
                                            (q1 ∨ p1) ∧ (q2 ∨ p2)
proof1 : myfavouritetheorem
proof1 = {! refl!}   -- this won't work, since p1 != q1, etc!
                     -- proving this manually would require 2ⁿ cases...

-- we'll make some DSL into which we're going to translate theorems
-- (which are actually types of functions), and then use reflection
-- in some magical way... TBC

open import Data.Nat
open import Data.Fin

data BoolExpr : ℕ → Set where
  Truth     : {n : ℕ}                           → BoolExpr n
  Falsehood : {n : ℕ}                           → BoolExpr n
  And       : {n : ℕ} → BoolExpr n → BoolExpr n → BoolExpr n
  Or        : {n : ℕ} → BoolExpr n → BoolExpr n → BoolExpr n
  Not       : {n : ℕ} → BoolExpr n              → BoolExpr n
  Imp       : {n : ℕ} → BoolExpr n → BoolExpr n → BoolExpr n
  Atomic    : {n : ℕ} → Fin n                   → BoolExpr n

open import Data.Vec
open import Data.Unit hiding (_≤?_)
open import Data.Empty
open import Data.Sum
open import Data.Product

-- ...and some way to interpret our representation
-- of the formula at hand:
-- this is compile : S → D

-- the environment
Env : ℕ → Set
Env = Vec Bool
  -- lijst van lengte n met daarin een Set / Bool

-- S = BoolExpr (the syntactic realm)
-- D = the domain of our Props
⟦_⊢_⟧ : {n : ℕ} → Env n → BoolExpr n → Set
⟦ env ⊢ Truth ⟧     = ⊤
⟦ env ⊢ Falsehood ⟧ = ⊥
⟦ env ⊢ And p q ⟧   = ⟦ env ⊢ p ⟧ × ⟦ env ⊢ q ⟧
⟦ env ⊢ Or p q ⟧    = ⟦ env ⊢ p ⟧ ⊎ ⟦ env ⊢ q ⟧
⟦ env ⊢ Imp p q ⟧   = ⟦ env ⊢ p ⟧ → ⟦ env ⊢ q ⟧
⟦ env ⊢ Atomic n ⟧ with lookup n env
... | true  = ⊤
... | false = ⊥
⟦ env ⊢ Not p ⟧     = ⟦ env ⊢ p ⟧ → ⊥ -- if you manage to prove p, then Not p cannot hold

-- decision procedure:
-- return whether the given proposition is true
-- this is like our isEvenQ
decide : ∀ {n : ℕ} (e : Env n) → BoolExpr n → Bool
decide env (Truth)      = true
decide env (Falsehood)  = false
decide env (And be be₁) = decide env be ∧ decide env be₁
decide env (Or be be₁)  = decide env be ∨ decide env be₁
decide env (Not p)      = not (decide env p)
decide env (Imp p q)    = not (decide env p) ∨ (decide env q)
decide env (Atomic n)   = lookup n env

-- these helpers show that a AND b => both a = true, as well as b = true.
and-l : ∀ {b b'} → b ∧ b' ≡ true → b ≡ true
and-l {true} eq = refl
and-l {false} eq = eq

and-r : ∀ b b' → b ∧ b' ≡ true → b' ≡ true
and-r true b' eq = eq
and-r false true eq = refl
and-r false false eq = eq

and-false : ∀ p q → p ∧ q ≡ false → p ≡ false ⊎ q ≡ false
and-false false q = inj₁
and-false true q  = inj₂

or-false-l : ∀ p q → p ∨ q ≡ false → p ≡ false
or-false-l true q  ()
or-false-l false q pf = refl

or-false-r : ∀ p q → p ∨ q ≡ false → q ≡ false
or-false-r true true ()
or-false-r false true ()
or-false-r p false pf = refl

or-lem : ∀ p q → p ∨ q ≡ true → p ≡ true ⊎ q ≡ true
or-lem true q  = inj₁
or-lem false q = inj₂

boolToAST : ∀ {n : ℕ} → Bool → BoolExpr n
boolToAST true  = Truth
boolToAST false = Falsehood

not-lemma : {b : Bool} → not b ≡ true → b ≡ false
not-lemma {false} refl = refl
not-lemma {true}  ()

not-false : {b : Bool} → not b ≡ false → b ≡ true
not-false {true}  pf = refl
not-false {false} ()

mutual
  -- first a helper for the cases where a proposition isn't true
  soundness' : {n : ℕ} → (env : Env n) → (p : BoolExpr n) → decide env p ≡ false → ⟦ env ⊢ p ⟧ → ⊥
  soundness' env Truth () pf
  soundness' env Falsehood dec  pf = pf
  soundness' env (And p p₁) dec pf  with and-false (decide env p) (decide env p₁) dec
  soundness' env (And p p₁) dec pf | inj₁ () --  = {!!}
  soundness' env (And p p₁) dec pf | inj₂ y = {!!}
  soundness' env (Or p p₁) dec  pf = {!!}
  soundness' env (Not p) dec    pf = pf (soundness env p (not-false dec))
  soundness' env (Imp p p₁) dec pf = {!!}
  soundness' env (Atomic x) dec pf = {!!}
  
  -- soundness theorem:
  soundness : {n : ℕ} → (env : Env n) → (p : BoolExpr n) → decide env p ≡ true → ⟦ env ⊢ p ⟧
  soundness env (Truth) refl = tt
  soundness env (Falsehood) ()
  soundness env (And p p₁) pf = (soundness env p  (and-l pf)) ,
                                (soundness env p₁ (and-r (decide env p) (decide env p₁) pf))
  soundness env (Or p p₁) pf  with or-lem (decide env p) (decide env p₁) pf
  soundness env (Or p p₁) pf | inj₁ x = inj₁ (soundness env p x)
  soundness env (Or p p₁) pf | inj₂ y = inj₂ (soundness env p₁ y)
  soundness env (Not p) pf = soundness' env p (not-lemma pf)
  soundness env (Imp p q) pf  with or-lem (decide env (Not p)) (decide env q) pf
  soundness env (Imp p q) pf | inj₁ y = λ x → ⊥-elim (soundness' env p (not-lemma y) x)
  soundness env (Imp p q) pf | inj₂ y = λ x → soundness env q y
  soundness env (Atomic n) pf with lookup n env
  soundness env (Atomic n₁) refl | .true = tt

open import Data.Nat
open import Relation.Nullary hiding (¬_)
open import Data.Product

-- still required: 
-- * do actual reflection
-- * prove soundness theorem
-- see lecture11.pdf

private
-- we can only prove "propositions" that eventually evaluate to true.
-- somethingIWantToProve : true ∨ false ≡ true
-- this should be formulated as follows:
-- you give the type in terms of the AST
-- of course, later we want to generate the AST ourselves.
    empty : Env zero
    empty = []

    somethingIWantToProve : ⟦ empty ⊢ Or (Truth) (Falsehood) ⟧
    somethingIWantToProve  = soundness empty (Or (Truth) (Falsehood)) refl

private

    -- this also works if you set oneVar = true :: []. Next
    -- we want to automatically prove all cases.
    -- how to do this automatically?
    thm0 : ∀ (ov : Env 1) → ⟦ ov ⊢ Or (Atomic zero) (Not (Atomic zero))⟧
    thm0 (true ∷ [])  = soundness (true ∷ []) (Or (Atomic zero) (Not (Atomic zero))) refl
    thm0 (false ∷ []) = soundness (false ∷ []) (Or (Atomic zero) (Not (Atomic zero))) refl

    thm1 : ∀ (ov : Env 1) → ⟦ ov ⊢ Imp (Atomic zero) (Atomic zero) ⟧
    --thm1 ov = soundness ov (Imp (Atomic zero) (Atomic zero)) refl
    thm1 (true ∷ []) = soundness (true ∷ []) (Imp (Atomic zero) (Atomic zero)) refl
    thm1 (false ∷ []) = soundness (false ∷ []) (Imp (Atomic zero) (Atomic zero)) refl
    
-- next step: automatically generate the AST from something like this:
-- theorem1 : Set
-- theorem1 = {p : Bool} → p ∨ ¬ p ≡ true
