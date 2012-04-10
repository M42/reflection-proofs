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
  Not   : BoolExpr            → BoolExpr
--   Impl  : BoolExpr → BoolExpr → BoolExpr

-- ...and some way to interpret our representation
-- of the formula at hand:
-- this is our compilation: happens to be like the decision
-- procedure, will differ for things other than bool
-- this is compile : S → D

-- S = BoolExpr (the syntactic realm)
-- D = the domain of our Props
⟦_⟧ : BoolExpr → Bool
⟦ Const true ⟧ = true
⟦ Const false ⟧ = false
⟦ And p q ⟧ = ⟦ p ⟧ ∧ ⟦ q ⟧
⟦ Or p q ⟧ = ⟦ p ⟧ ∨ ⟦ q ⟧
⟦ Not p ⟧ = not ⟦ p ⟧
-- ⟦ Impl p q ⟧ = not ⟦ p ⟧ ∨ ⟦ q ⟧ -- logical implication
-- and if we encounter a variable, same name => equal

-- decision procedure:
-- return whether the given proposition is true
decide : BoolExpr → Bool
decide (Const true) = true
decide (Const false) = false
decide (And be be₁) = decide be ∧ decide be₁
decide (Or be be₁) = decide be ∨ decide be₁
decide (Not be) = not (decide be)

-- soundness:
soundness : (p : BoolExpr) → decide p ≡ true → ⟦ p ⟧ ≡ true
soundness (Const true) refl = refl
soundness (Const false) ()
soundness (And p p₁) pf = {!!}
soundness (Or p p₁) pf = {!!}
soundness (Not p) pf = soundness {!p!} pf

-- getting back to our nicer formulation:

open import Reflection
open import Data.Nat
open import Relation.Nullary hiding (¬_)
open import Data.List
open import Data.Product

easiertheorem : Set
easiertheorem = true ∨ false ≡ true

--------------------------------------------
-- Extracting two sides of the equation --
--------------------------------------------

≡' : Name
≡' = quote _≡_

-- returns true iff the term is the equality type,
-- ie. states the equality of two objects

isEquality : Term → Bool
isEquality (def f args) with f ≟-Name ≡'
isEquality (def f args) | yes p with args
isEquality (def f args) | yes p | x ∷ x₁ ∷ x₂ ∷ x₃ ∷ l = true

-- false otherwise
isEquality (def f args) | yes p | [] = false
isEquality (def f args) | yes p | x ∷ [] = false
isEquality (def f args) | yes p | x ∷ x₁ ∷ [] = false
isEquality (def f args) | yes p | x ∷ x₁ ∷ x₂ ∷ [] = false
isEquality (def f args) | no ¬p = false
isEquality (var x args) = false
isEquality (con c args) = false
isEquality (lam v t) = false
isEquality (pi t₁ t₂) = false
isEquality (sort x) = false
isEquality unknown = false

private
  isEquality-ex : ∀ m n → true ≡ isEquality (quoteTerm (m + n ≡ n + m))
  isEquality-ex = λ m n → refl


-- returns (L , R) given L ≡ R and tt otherwise
-- takes a precondition so we don't have to polute our program with Maybes

extractEqParts : (t : Term) → .(eq : isEquality t ≡ true) → Term × Term
extractEqParts (def f args) eq with f ≟-Name ≡'
extractEqParts (def f args) eq | yes p with args
extractEqParts (def f args) eq | yes p | x ∷ x₀ ∷ arg v r lhs ∷ arg v₁ r₁ rhs ∷ l
  = lhs , rhs

-- non-equality cases with false precondition
extractEqParts (def f args) () | yes p | []
extractEqParts (def f args) () | yes p | x ∷ []
extractEqParts (def f args) () | yes p | x ∷ x₁ ∷ []
extractEqParts (def f args) () | yes p | x ∷ x₁ ∷ x₂ ∷ []
extractEqParts (def f args) () | no ¬p
extractEqParts (var x args) ()
extractEqParts (con c args) ()
extractEqParts (lam v t) ()
extractEqParts (pi t₁ t₂) ()
extractEqParts (sort x) ()
extractEqParts unknown ()

-- projections for particular sides of the equation

lhs : (t : Term) → .(eq : isEquality t ≡ true) → Term
lhs t eq = proj₁ (extractEqParts t eq)

rhs : (t : Term) → .(eq : isEquality t ≡ true) → Term
rhs t eq = proj₂ (extractEqParts t eq)

-- Reflecting the structure of a term into a boolean expression

-- quoted names

true' : Name
true' = quote Data.Bool.true
false' : Name
false' = quote Data.Bool.false
and' : Name
and' = quote Data.Bool._∧_
or' : Name
or' = quote Data.Bool._∨_
not' : Name
not' = quote Data.Bool.not

-- a function that checks if a given term is a boolean expression
-- n is the number of free variables in the term of type Bool

isBoolExpr : {n : ℕ} → Term → Bool
isBoolExpr {n} (var x args)  with suc x ≤? n
isBoolExpr (var x args) | yes p = true     -- huh?
isBoolExpr (var x args) | no ¬p = false
isBoolExpr (con c args)  with c ≟-Name false'
isBoolExpr (con c args) | yes p = true
isBoolExpr (con c args) | no ¬p  with c ≟-Name true'
isBoolExpr (con c args) | no ¬p  | yes p = true
isBoolExpr (con c args) | no ¬p₁ | no ¬p = false
isBoolExpr (def f []) = false
isBoolExpr {n} (def f (arg v r x ∷ args))  with f ≟-Name not'
...                             | yes p = isBoolExpr {n} x
isBoolExpr (def f (arg v r x ∷ [])) | no ¬p = false -- wrong number of args?
isBoolExpr (def f (arg v r x ∷ x₁ ∷ args)) | no ¬p  with f ≟-Name and'
isBoolExpr {n} (def f (arg v r x ∷ arg v1 r1 x1 ∷ args)) | no ¬p | yes p = (isBoolExpr {n} x) ∧ (isBoolExpr {n} x1)
isBoolExpr (def f (arg v r x ∷ x₁ ∷ args)) | no ¬p₁ | no ¬p  with f ≟-Name or'
isBoolExpr {n} (def f (arg v r x ∷ arg v1 r1 x1 ∷ args)) | no ¬p₁ | no ¬p | yes p = (isBoolExpr {n} x) ∧ (isBoolExpr {n} x1)
isBoolExpr (def f (arg v r x ∷ x₁ ∷ args)) | no ¬p₂ | no ¬p₁ | no ¬p = false
isBoolExpr (lam v t) = false
isBoolExpr (pi t₁ t₂) = false
isBoolExpr (sort x) = false
isBoolExpr unknown = false

private
  -- examples of reasonable boolean expressions
  isBoolExpr-ex1 : isBoolExpr {0} (quoteTerm true) ≡ true
  isBoolExpr-ex1 = refl
  isBoolExpr-ex2 : isBoolExpr {0} (quoteTerm ( ¬ (¬ (true ∧ false )) )) ≡ true
  isBoolExpr-ex2 = refl
  isBoolExpr-ex3 : isBoolExpr {0} (quoteTerm ( ¬ (¬ (( ¬ false) ∧ false )) )) ≡ true
  isBoolExpr-ex3 = refl
  isBoolExpr-ex4 : (p : Bool) → isBoolExpr {1} (quoteTerm ( ¬ (¬ (( ¬ false) ∧ p )) )) ≡ true
  isBoolExpr-ex4 p = refl
  
-- Boolean helpers
-- Agda is able to infer b and b' in and-l but not in and-r, hence the contrast.

private

  and-l : ∀ {b b'} → b ∧ b' ≡ true → b ≡ true
  and-l {true} eq = refl
  and-l {false} eq = eq

  and-r : ∀ b b' → b ∧ b' ≡ true → b' ≡ true
  and-r true b' eq = eq
  and-r false true eq = refl
  and-r false false eq = eq

-- The main reflection helper.
-- Takes a term that is known to have the structure of a polynomial and
-- reflects its structure.


-- still required: 
-- * do actual reflection
-- * evaluate the DSL AST we get
-- * prove soundness theorem
-- see lecture11.pdf



somethingIWantToProve : true ≡ true ∨ false
somethingIWantToProve  = quoteGoal e in soundness e refl


-- next step: variables:
theorem1 : Set
theorem1 = {p : Bool} → p ∨ ¬ p ≡ p

