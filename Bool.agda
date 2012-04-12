module Bool where

open import Relation.Binary.PropositionalEquality
open import Data.Bool

¬_ : Bool → Bool
¬_ = not

-- here's something the type system gives us
-- for free: (i.e. not not true is evaluated,
-- then refl works)
trueisnotnottrue : true ≡ ¬ ( ¬ true)
trueisnotnottrue = refl

myfavouritetheorem : Set
myfavouritetheorem = {p1 q1 p2 q2 : Bool} → (p1 ∨ q1) ∧ (p2 ∨ q2) ≡
                                            (q1 ∨ p1) ∧ (q2 ∨ p2)
proof1 : myfavouritetheorem
proof1 = {! refl!}   -- this won't work, since p1 != q1, etc!
                    -- proving this manually would require 2ⁿ cases...

-- we'll make some DSL into which we're going to translate theorems
-- (which are actually types of functions), and then use reflection
-- in some magical way... TBC

data BoolExpr : Set where
  Const : Bool                → BoolExpr
  And   : BoolExpr → BoolExpr → BoolExpr
  Or    : BoolExpr → BoolExpr → BoolExpr
--  Not   : BoolExpr            → BoolExpr
--  Is    : Bool → Bool → BoolExpr
--   Impl  : BoolExpr → BoolExpr → BoolExpr

-- ...and some way to interpret our representation
-- of the formula at hand:
-- this is our compilation: happens to be like the decision
-- procedure, will differ for things other than bool
-- this is compile : S → D

open import Data.Unit hiding (_≤?_)
open import Data.Empty
open import Data.Sum
open import Data.Product

-- S = BoolExpr (the syntactic realm)
-- D = the domain of our Props
⟦_⟧ : BoolExpr → Set
⟦ Const true ⟧ = ⊤
⟦ Const false ⟧ = ⊥
⟦ And p q ⟧ = ⟦ p ⟧ × ⟦ q ⟧
⟦ Or p q ⟧ = ⟦ p ⟧ ⊎ ⟦ q ⟧
-- ⟦ Not p ⟧ with ⟦ p ⟧
-- ⟦ Is p q ⟧ = {!!}
-- ⟦ Impl p q ⟧ = not ⟦ p ⟧ ∨ ⟦ q ⟧ -- logical implication
-- and if we encounter a variable, same name => equal

-- decision procedure:
-- return whether the given proposition is true
-- this is like our isEvenQ
decide : BoolExpr → Bool
decide (Const true) = true
decide (Const false) = false
decide (And be be₁) = decide be ∧ decide be₁
decide (Or be be₁) = decide be ∨ decide be₁
-- decide (Not be) = not (decide be)
-- decide (Is p q) = {!!}

and-l : ∀ {b b'} → b ∧ b' ≡ true → b ≡ true
and-l {true} eq = refl
and-l {false} eq = eq

and-r : ∀ b b' → b ∧ b' ≡ true → b' ≡ true
and-r true b' eq = eq
and-r false true eq = refl
and-r false false eq = eq
-- soundness:
soundness : (p : BoolExpr) → decide p ≡ true → ⟦ p ⟧
soundness (Const true) refl = tt
soundness (Const false) ()
soundness (And p p₁) pf = (soundness p  (and-l pf)) ,
                          (soundness p₁ (and-r (decide p) (decide p₁) pf))
soundness (Or p p₁) pf  = {!pf!}
-- soundness (Not p) pf = soundness {!p!} pf
-- soundness (Is p q) pf = {!!}

-- getting back to our nicer formulation:

open import Data.Nat
open import Relation.Nullary hiding (¬_)
open import Data.List
open import Data.Product



-- still required: 
-- * do actual reflection
-- * prove soundness theorem
-- see lecture11.pdf


-- we can only prove "propositions" that eventually evaluate to true.
-- somethingIWantToProve : true ∨ false ≡ true
-- this should be formulated as follows:
-- you give the type in terms of the AST
-- of course, later we want to generate the AST ourselves.
somethingIWantToProve : ⟦ Or (Const true) (Const false) ⟧
somethingIWantToProve  = soundness (Or (Const true) (Const false)) refl


-- next step: variables:
-- theorem1 : Set
theorem1 = {p : Bool} → p ∨ ¬ p ≡ true
