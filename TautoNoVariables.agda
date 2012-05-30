{-# OPTIONS --type-in-type #-}
module TautoNoVariables where

open import Relation.Binary.PropositionalEquality renaming ( [_] to by ; subst to substpe)
open import Lemmas
open import Data.Maybe hiding (Eq)
open import Data.Nat
open import Relation.Nullary hiding (¬_)
open import Data.Product hiding (map)
open import Data.Vec.Properties
open import Data.Nat.Properties
open import Relation.Binary hiding (_⇒_)
open import Reflection

open import Data.Vec.N-ary
open import Data.Bool renaming (not to ¬_)
open import Data.Nat
open import Data.Fin hiding (_+_; pred)
open import Data.Vec renaming (reverse to vreverse ; map to vmap; foldr to vfoldr; _++_ to _v++_)
open import Data.Unit hiding (_≤?_)
open import Data.Empty
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.List

open import Relation.Binary.PropositionalEquality.TrustMe

_⇒_ : Bool → Bool → Bool
true  ⇒ true  = true
true  ⇒ false = false
false ⇒ true  = true
false ⇒ false = true

-- here's an example of a manual proof (not so complex in this case, unfortunately.)
trueandtrue : true ∧ true ⇒ true ∨ false ≡ true
trueandtrue = refl


-- wouldn't it be nice if we could automate this?



-- we'll make some DSL into which we're going to translate theorems
-- (which are actually types of functions), and then use reflection
-- in some unmagical way... see below.

{-
The point of having SET is to have a place to put stuff subst gives us.
i.e., if we want to go from BoolExpr -> Set, we need a way to reattach a
variable in the Pi type to some term inside our boolean expression.
-}
data BoolExpr : Set where
  Truth     :                       BoolExpr
  Falsehood :                       BoolExpr
  And       : BoolExpr → BoolExpr → BoolExpr
  Or        : BoolExpr → BoolExpr → BoolExpr
  Imp       : BoolExpr → BoolExpr → BoolExpr

-- ...and some way to interpret our representation
-- of the formula at hand:
-- this is compile : S → D


-- S = BoolExpr (the syntactic realm)
-- D = the domain of our Props
⟦_⟧ : BoolExpr → Bool
⟦ Truth ⟧     = true
⟦ Falsehood ⟧ = false
⟦ And p q ⟧   = ⟦ p ⟧ ∧ ⟦ q ⟧
⟦ Or p q ⟧    = ⟦ p ⟧ ∨ ⟦ q ⟧
⟦ Imp p q ⟧   = ⟦ p ⟧ ⇒ ⟦ q ⟧



-- decision procedure:
-- return whether the given proposition is true
-- this is like our isEvenQ
decide : BoolExpr → Bool
decide (Truth)      = true
decide (Falsehood)  = false
decide (And be be₁) = decide be ∧ decide be₁
decide (Or be be₁)  = decide be ∨ decide be₁
decide (Imp p q)    = ¬ decide p ∨ decide q


mutual
  -- first a helper for the cases where a proposition isn't true
  soundness' : (p : BoolExpr) → decide p ≡ false → ⟦ p ⟧ ≡ true → ⊥
  soundness' Truth () pf
  soundness' Falsehood dec  pf = {!pf!}
  soundness' (And p q) dec pf  with and-false (decide p) (decide q) dec
  soundness' (And p q) dec pf | inj₁ x = soundness' p x {!!}
  soundness' (And p q) dec pf | inj₂ y = soundness' q y {!!}
  soundness' (Or p q)  dec pf  with or-false (decide p) (decide q) dec
  soundness' (Or p q)  dec pf | proj₁ , proj₂ = soundness' p proj₁ {!!}
 -- soundness' (Or p q)  dec pf | proj₁ , proj₂ = soundness' q proj₂ ?
  soundness' (Imp p q) dec pf = {!!}
  -- soundness' (Imp p q) dec pf  with or-false (¬ (decide p)) (decide q) dec
  -- soundness' (Imp p q) dec pf | proj₁ , proj₂  with not-false proj₁
  -- ... | tmppat  with pf (soundness p tmppat)
  -- ... | tmppatq = soundness' q proj₂ tmppatq

  -- soundness theorem:
  soundness : (p : BoolExpr) → decide p ≡ true → ⟦ p ⟧ ≡ true
  soundness (Truth) refl = {!!}
  soundness (Falsehood) ()
  soundness (And p p₁) pf = {!!} --   (soundness p  (and-l pf)) ,
                              --   (soundness p₁ (and-r (decide p) (decide p₁) pf))
  soundness (Or p p₁) pf  with or-lem (decide p) (decide p₁) pf
  soundness (Or p p₁) pf | inj₁ x = {!!} -- inj₁ (soundness p x)
  soundness (Or p p₁) pf | inj₂ y = {!!} -- inj₂ (soundness p₁ y)
  soundness (Imp p q) pf  with or-lem (¬ (decide p)) (decide q) pf
  soundness (Imp p q) pf | inj₁ y = {!!} -- λ x → ⊥-elim (soundness' p (not-lemma y) x)
  soundness (Imp p q) pf | inj₂ y = {!!} -- λ x → soundness q y


private
-- we can only prove "propositions" that eventually evaluate to true.
-- somethingIWantToProve : true ∨ false ≡ true
-- this should be formulated as follows:
-- you give the type in terms of the AST
-- of course, later we want to generate the AST ourselves.

    somethingIWantToProve : ⟦ Or (Truth) (Falsehood) ⟧ ≡ true
    somethingIWantToProve  = soundness (Or (Truth) (Falsehood)) refl

private
    -- this also works if you set oneVar = true :: []. Next
    -- we want to automatically prove all cases.
    -- how to do this automatically?
    thm0 : ⟦ Or (Truth) (Imp (Falsehood) (Truth))⟧ ≡ true
    thm0 = soundness (Or (Truth) (Imp Falsehood (Truth))) refl

    thm1 : ⟦ Imp (Truth) (Truth) ⟧ ≡ true
    --thm1 ov = soundness ov (Imp (Atomic zero) (Atomic zero)) refl
    thm1 = soundness (Imp (Truth) (Truth)) refl

-- next step: try and avoid having to enumerate all the possible environments,
-- as this will quickly become tedious (and remember, the challenge was to
-- prove tautologies in n² and not 2ⁿ with n the number of variables...

-- First: return proof either way, not maybe, from automate,
-- then: prove that you can enumerate all possible Env's and use
-- that to call decide...

-- okay, next attempt: using quoteGoal


≡' : Name
≡' = quote _≡_

ff : Name
ff = quote false

-- returns the number of the outermost pi quantified variables.

-- peels off all the outermost Pi constructors,
-- returning a term with argsNo free variables.


-- someThm : ∀ {p1 p2 q1 q2} → ((p1 ∨ q1) ∧ (p2 ∨ q2)) ⇒ ((q1 ∨ p1) ∧ (q2 ∨ p2)) ≡ true
-- someThm = quoteGoal g in {! (lhs g refl)!} -- C-c C-n in this goal is useful.


  
  -- simplefied notation, non-executable
  -- stripPi-ex : stripPi-ex t ≡ def ≡' (var 2 + var 1) ≡ (var 1 + var 0)

outerIsEq : (t : Term) → Bool
outerIsEq (var x args) = false
outerIsEq (con c args) = false
outerIsEq (def f (a ∷ b ∷ c ∷ (arg _ _ (con ff [])) ∷ [])) with f ≟-Name ≡'
... | yes p = true
... | no ¬p = false
outerIsEq (def f as)   = false
outerIsEq (lam v t)    = false
outerIsEq (pi t₁ t₂)   = false
outerIsEq (sort x)     = false
outerIsEq unknown      = false

noEQ : (t : Term) → outerIsEq t ≡ true → Term
noEQ (var x args) ()
noEQ (con c args) ()
noEQ (def f []) ()
noEQ (def f (x ∷ [])) ()
noEQ (def f (x ∷ x₁ ∷ [])) ()
noEQ (def f (x ∷ x₁ ∷ x₂ ∷ [])) ()
noEQ (def f (x ∷ x₁ ∷ x₂ ∷ (arg _ _ (con ff [])) ∷ [])) pf with f ≟-Name ≡'
noEQ (def f (x ∷ x₁ ∷ arg v r x₂ ∷ arg v₁ r₁ (con ff []) ∷ [])) pf | yes p = x₂
noEQ (def f (x ∷ x₁ ∷ x₂ ∷ arg v r (con ff []) ∷ [])) () | no ¬p
noEQ (def f (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])) ()
noEQ (def f (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ args)) ()
noEQ (lam v t) ()
noEQ (pi t₁ t₂) ()
noEQ (sort x) ()
noEQ unknown ()


isBoolExprQ' : (t : Term) → Bool
isBoolExprQ' (var x args) = false
isBoolExprQ' (con c args) with c ≟-Name (quote false)
isBoolExprQ' (con c args) | yes p = true
isBoolExprQ' (con c args) | no ¬p with c ≟-Name (quote true)
isBoolExprQ' (con c args) | no ¬p | yes p = true
isBoolExprQ' (con c args) | no ¬p₁ | no ¬p = false
isBoolExprQ' (def f args) with f ≟-Name (quote Data.Bool._∧_)
isBoolExprQ' (def f (_ ∷ _ ∷ arg _ _ t₁ ∷ arg _ _ t₂ ∷ [])) | yes p = _∧_ (isBoolExprQ' t₁) (isBoolExprQ' t₂)
isBoolExprQ' (def f _) | yes p = false
isBoolExprQ' (def f args) | no p  with f ≟-Name (quote Data.Bool.false)
isBoolExprQ' (def f []  ) | no _ | yes p = true
isBoolExprQ' (def f args) | no _ | yes p = false
isBoolExprQ' (def f args) | no _ | no  p with f ≟-Name (quote Data.Bool._∨_)
isBoolExprQ' (def f (_ ∷ _ ∷ arg _ _ t₁ ∷ arg _ _ t₂ ∷ [])) | no _ | no _ | yes p = _∧_ (isBoolExprQ' t₁)
                                                                                 (isBoolExprQ' t₂)
isBoolExprQ' (def f args) | no _ | no _ | yes _  = false
isBoolExprQ' (def f args) | no _ | no _ | no _ with f ≟-Name (quote Data.Bool.true)
isBoolExprQ' (def f []) | no _   | no _    | no _    | yes _ = true
isBoolExprQ' (def f _ ) | no _   | no _    | no _    | yes _ = false
isBoolExprQ' (def f _ ) | no _   | no _    | no _    | no _  = false

isBoolExprQ' (lam v t') = isBoolExprQ' t'
isBoolExprQ' (pi (arg visible relevant (el _ t₁)) (el _ t₂)) = _∧_ (isBoolExprQ' t₁) (isBoolExprQ' t₂)
isBoolExprQ' (sort x )= false
isBoolExprQ' (unknown) = false
isBoolExprQ' (pi _ _) = false


isBoolExprQ : (t : Term) → outerIsEq t ≡ true → Bool
isBoolExprQ t pf with noEQ t pf
isBoolExprQ t pf | t' = isBoolExprQ' t'

term2b : (t : Term) → isBoolExprQ t {!!} ≡ true → BoolExpr
term2b t pf with noEQ t {!!}
term2b t pf | var x args = {!!}
term2b t pf | con c args with c ≟-Name (quote true)
term2b t pf | con c args | yes p = Truth
term2b t pf | con c args | no ¬p with c ≟-Name (quote false)
term2b t pf | con c args | no ¬p | yes p = Falsehood
term2b t pf | con c args | no ¬p₁ | no ¬p = {!pf!}
term2b t pf | def f args = {!!}
term2b t pf | lam v t' = {!!}
term2b t pf | pi t₁ t₂ = {!!}
term2b t pf | sort x = {!!}
term2b t pf | unknown = {!!}

private
  -- here we'll test the reflection a bit
  -- sort of like a few unit tests...
  test0 : Set
  test0 = (a b c d : Bool) → a ∧ b ≡ true

 --  test0-check : let t = quoteTerm test0 in
 --                term2b (argsNo t) 0 t refl ≡ And (Atomic (suc (suc (suc zero)))) (Atomic (suc (suc zero)))
 --  test0-check = refl
 --  test1-check : let t = quoteTerm ( (a b d : Set) → a → b) in
 --                term2b (argsNo t) 0 t refl ≡ Imp (Atomic ((suc (suc zero)))) (Atomic ((suc zero)))
 --  test1-check = refl
 --  test2-check : let t = quoteTerm ( (a b c : Set) → a ∧ c → b ) in
 --                term2b (argsNo t) 0 t refl ≡ Imp (And (Atomic (suc (suc zero))) (Atomic zero)) (Atomic (suc zero))
 --  test2-check = refl
 --  test3-check : let t = quoteTerm ( (a b c d : Set) → ¬ a → b ) in
 --                term2b (argsNo t) 0 t refl ≡ Imp (Imp Falsehood (Atomic (suc (suc (suc zero))))) (Atomic (suc (suc zero)))
 --  test3-check = refl
--   test4-check : let t = quoteTerm ( (a b c d : Set) → ⊥ ∨ b ) in
--                 term2b (argsNo t) 0 t refl ≡ Or (Falsehood) (Atomic (suc (suc zero)))
--   test4-check = refl


{-
TODO:
- enforce that the environments are what you'd expect (i.e. prepend false right, true left,
  when building up tree
-}

exp0 : BoolExpr
exp0 = Imp Truth Truth

exp1 : BoolExpr
exp1 = Imp (Truth) (Truth)


-- this is actually our soundness function.

somethm : Set
somethm = (true ⇒ true ∨ true) ∧ (false ∨ true) ≡ true

goalbla : somethm
goalbla = quoteGoal e in soundness (term2b e refl) refl -- automate2 (term2b (argsNo e) 0 (stripPi e) ?) {!!}


-- next up!! using foo, find forallEnvs n (\ e -> [[ b ]] e)
-- possible using Tree.
