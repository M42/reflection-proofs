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
open ≡-Reasoning
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

-- here's an example of a manual proof
trueandtrue : true ∧ true ⇒ true ≡ true
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
  soundness' Falsehood dec  pf = {!!}
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


-- still required:
-- * do actual reflection

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


-- TODO write a version which returns a
-- proof either way, not a maybe. possibly using a predicate to be instantiated
-- to refl?
automate : (p : BoolExpr) → Maybe (⟦ p ⟧ ≡ true)
automate p  with decide p | inspect (decide ) p
automate p | true  | by eq = just (soundness p eq)
automate p | false | by eq = nothing

private
  thm2 : ⟦ Or (Truth) (Imp Falsehood (Truth))⟧ ≡ true
  thm2  with automate (Or (Truth) (Imp Falsehood (Truth)))
  thm2 | just x = x
  thm2 | nothing = {!!}

  thm3 : ⟦ Imp (Truth) (Truth) ⟧ ≡ true
  thm3  with automate (Imp (Truth) (Truth))
  thm3 | just x = x
  thm3 | nothing = {!!}

  o  : Fin 4
  o  = suc zero
  t  : Fin 4
  t  = suc (suc zero)
  th : Fin 4
  th = suc (suc (suc zero))

  -- this means the following: ((p1 ∨ q1) ∧ (p2 ∨ q2) → (q1 ∨ p1) ∧ (q2 ∨ p2))
  -- ...which is cool, since we can now prove tautologies of this form.
  thm1bdef : BoolExpr
  thm1bdef = Imp (And (Or (Truth) (Truth)) (Or (Truth) (Truth)))
                 (And (Or (Truth) (Truth)) (Or (Truth) (Truth)))

  thm1b : ⟦ thm1bdef ⟧ ≡ true
  thm1b with automate thm1bdef
  thm1b | just x = x
  thm1b | nothing = {!!} -- we want absurd here.

-- First: return proof either way, not maybe, from automate,
-- then: prove that you can enumerate all possible Env's and use
-- that to call decide...

-- okay, next attempt: using quoteGoal


≡' : Name
≡' = quote _≡_

-- returns the number of the outermost pi quantified variables.

argsNo : Term → ℕ
argsNo (pi (arg visible relevant (el (lit _) (sort (lit _)))) (el s t)) = suc (argsNo t)
-- argsNo (pi (arg visible relevant (el (lit 0) (def  _ _))) (el s t)) = suc (argsNo t)
argsNo (var x args) = 0
argsNo (con c args) = 0
argsNo (def f args) = 0
argsNo (lam v t)    = 0
argsNo (sort x)     = 0
argsNo unknown      = 0
argsNo _            = 0

-- peels off all the outermost Pi constructors,
-- returning a term with argsNo free variables.

stripPi : Term → Term
stripPi (pi (arg visible relevant (el (lit _) (sort (lit _)))) (el s t)) = stripPi t
--stripPi (pi (arg visible relevant (el (lit 0) (def  _ _))) (el s t)) = stripPi t
-- identity otherwise
stripPi (pi args t)  = pi   args t
stripPi (var x args) = var  x    args
stripPi (con c args) = con  c    args
stripPi (def f args) = def  f    args
stripPi (lam v t)    = lam  v    t
stripPi (sort x)     = sort x
stripPi unknown      = unknown

allTrue : List Bool → Bool
allTrue = foldr _∧_ true

someThm : ∀ {p1 p2 q1 q2} → ((p1 ∨ q1) ∧ (p2 ∨ q2)) ⇒ ((q1 ∨ p1) ∧ (q2 ∨ p2)) ≡ true
someThm = quoteGoal g in {! (lhs g refl)!} -- C-c C-n in this goal is useful.


-- examples

private

  term-ex₁ : Term
  term-ex₁ = quoteTerm ((a b c d : Set) → b → a)

  argsNo-ex₁ : argsNo term-ex₁ ≡ 4
  argsNo-ex₁ = refl
  
  -- simplefied notation, non-executable
  -- stripPi-ex : stripPi-ex t ≡ def ≡' (var 2 + var 1) ≡ (var 1 + var 0)


unsafeMinus : (a : ℕ) → (b : ℕ) → ℕ
unsafeMinus zero m = zero
unsafeMinus n₁ zero = n₁
unsafeMinus (suc n₁) (suc m) = unsafeMinus n₁ m

isBoolExprQ : (n : ℕ) → (depth : ℕ) → (t : Term) → Bool
isBoolExprQ n depth t with stripPi t
isBoolExprQ n depth t | var x args with suc (unsafeMinus x depth) ≤? n
isBoolExprQ n depth t | var x args | yes p2 = true
isBoolExprQ n depth t | var x args | _      = true -- huh? 
isBoolExprQ n depth t | con c args = false
isBoolExprQ n depth t | def f args with f ≟-Name (quote Data.Product.Σ)
isBoolExprQ n depth t | def f (_ ∷ _ ∷ arg _ _ t₁ ∷ arg _ _ t₂ ∷ []) | yes p = _∧_ (isBoolExprQ n depth t₁) (isBoolExprQ n depth t₂)
isBoolExprQ n depth t | def f (_) | yes p = false
isBoolExprQ n depth t | def f args | no p  with f ≟-Name (quote Data.Empty.⊥)
isBoolExprQ n depth t | def f []   | no _ | yes p = true
isBoolExprQ n depth t | def f args | no _ | yes p = false
isBoolExprQ n depth t | def f args | no _ | no  p with f ≟-Name (quote Data.Sum._⊎_)
isBoolExprQ n depth t | def f (_ ∷ _ ∷ arg _ _ t₁ ∷ arg _ _ t₂ ∷ []) | no _ | no _ | yes p = _∧_ (isBoolExprQ n depth t₁)
                                                                                           (isBoolExprQ n depth t₂)
isBoolExprQ n depth t | def f args | no _ | no _ | yes _  = false
isBoolExprQ n depth t | def f args | no _ | no _ | no _ with f ≟-Name (quote Data.Unit.⊤)
isBoolExprQ n depth t | def f [] | no _   | no _    | no _    | yes _ = true
isBoolExprQ n depth t | def f _  | no _   | no _    | no _    | yes _ = false
isBoolExprQ n depth t | def f _  | no _   | no _    | no _    | no _  = false

isBoolExprQ n depth t | lam v t' = isBoolExprQ n (suc depth) t'
isBoolExprQ n depth t | pi (arg visible relevant (el _ t₁)) (el _ t₂) = _∧_ (isBoolExprQ (argsNo t₁) depth t₁) (isBoolExprQ n (suc depth) t₂)
isBoolExprQ n depth t | sort x = false
isBoolExprQ n depth t | unknown = false
isBoolExprQ n depth t | pi _ _ = false

-- we don't have a branch for Not, since that is immediately
-- translated as "¬ P ⇒ λ ⊥ → P"
term2b : (n : ℕ) → (depth : ℕ) → (t : Term) → isBoolExprQ (argsNo t) 0 t ≡ true → BoolExpr
term2b n depth t pf with stripPi t
term2b n depth t pf | var x args with suc (unsafeMinus x depth) ≤? n
term2b n depth t pf | var x args | yes p2 = {!!}
term2b n depth t () | var x args | _
term2b n depth t () | con c args
term2b n depth t pf | def f args with f ≟-Name (quote Data.Product.Σ)
term2b n depth t pf | def f (_ ∷ _ ∷ arg _ _ t₁ ∷ arg _ _ t₂ ∷ []) | yes p = And (term2b n depth t₁ (and-l {!!})) (term2b n depth t₂ (and-r {!!} {!!} pf))
term2b n depth t () | def f (_) | yes p
term2b n depth t pf | def f args | no p  with f ≟-Name (quote Data.Empty.⊥)
term2b n depth t pf | def f []   | no _ | yes p = Falsehood
term2b n depth t () | def f args | no _ | yes p
term2b n depth t pf | def f args | no _ | no  p with f ≟-Name (quote Data.Sum._⊎_)
term2b n depth t pf | def f (_ ∷ _ ∷ arg _ _ t₁ ∷ arg _ _ t₂ ∷ []) | no _ | no _ | yes p = Or (term2b n depth t₁ (and-l {!!}))
                                                                                              (term2b n depth t₂ (and-r (isBoolExprQ (argsNo t₁) 0 t₁) (isBoolExprQ (argsNo t₂) 0 t₂) {!!}))
term2b n depth t () | def f args | no _ | no _ | yes _
term2b n depth t pf | def f args | no _ | no _ | no _ with f ≟-Name (quote Data.Unit.⊤)
term2b n depth t pf | def f [] | no _   | no _    | no _    | yes _ = Truth
term2b n depth t () | def f _ | no _   | no _    | no _    | yes _ 
term2b n depth t () | def f _  | no _   | no _    | no _    | no _
                   
term2b n depth t pf | lam v t' = term2b n (suc depth) t' {!!}
term2b n depth t pf | pi (arg visible relevant (el _ t₁)) (el _ t₂) = Imp (term2b n depth t₁ {!!}) (term2b n (suc depth) t₂ {!!})
term2b n depth t () | sort x
term2b n depth t () | unknown
term2b n depth t () | pi _ _

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
-
-}

exp0 : BoolExpr
exp0 = Imp Truth Truth

exp1 : BoolExpr
exp1 = Imp (Truth) (Truth)


-- this is actually our soundness function.

somethm : Set
somethm = (a b c : Bool) → (b ⇒ b ∨ true) ∧ (c ∨ ¬ c) ≡ true

goalbla : somethm
goalbla = quoteGoal e in {!!} -- automate2 (term2b (argsNo e) 0 (stripPi e) ?) {!!}


-- next up!! using foo, find forallEnvs n (\ e -> [[ b ]] e)
-- possible using Tree.
