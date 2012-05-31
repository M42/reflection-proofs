{-# OPTIONS --type-in-type #-}
module TautoBoolVariables where

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
true ⇒ true = true
true ⇒ false = false
false ⇒ q = true

-- here's an example of a manual proof
trueandtrue : true ∧ true ⇒ true ≡ true
trueandtrue = refl

-- or, another one:
bOrNotb : (b : Bool) → b ∨ ¬ b ≡ true
bOrNotb true  = refl
bOrNotb false = refl

-- wouldn't it be nice if we could automate this?

-- eventually we'd like to prove these kinds of tautologies:
myfavouritetheorem : Set
myfavouritetheorem = (p1 q1 p2 q2 : Bool) → (p1 ∨ q1) ∧ (p2 ∨ q2)
                                          ⇒ (q1 ∨ p1) ∧ (q2 ∨ p2)
                                          ≡ true

proof1 : myfavouritetheorem
proof1 = {!!}   -- this is painful, since p1 != q1, etc
                -- proving this manually would require 2ⁿ cases...

-- we'll make some DSL into which we're going to translate theorems
-- (which are actually types of functions), and then use reflection
-- in some unmagical way... see below.

{-
The point of having SET is to have a place to put stuff subst gives us.
i.e., if we want to go from BoolExpr -> Set, we need a way to reattach a
variable in the Pi type to some term inside our boolean expression.
-}
data BoolExpr : ℕ → Set where
  Truth     : {n : ℕ}                           → BoolExpr n
  Falsehood : {n : ℕ}                           → BoolExpr n
  And       : {n : ℕ} → BoolExpr n → BoolExpr n → BoolExpr n
  Or        : {n : ℕ} → BoolExpr n → BoolExpr n → BoolExpr n
  Imp       : {n : ℕ} → BoolExpr n → BoolExpr n → BoolExpr n
  Atomic    : {n : ℕ} → Fin n                   → BoolExpr n

-- ...and some way to interpret our representation
-- of the formula at hand:
-- this is compile : S → D

-- the environment
Env : ℕ → Set
Env = Vec Bool
  -- lijst van lengte n met daarin een Set / Bool

-- S = BoolExpr (the syntactic realm)
-- D = the domain of our Props

⟦_⊢_⟧' : {n : ℕ} → Env n → BoolExpr n → Bool
⟦ env ⊢ Truth ⟧'     = true
⟦ env ⊢ Falsehood ⟧' = false
⟦ env ⊢ And p q ⟧'   = ⟦ env ⊢ p ⟧' ∧ ⟦ env ⊢ q ⟧'
⟦ env ⊢ Or p q ⟧'    = ⟦ env ⊢ p ⟧' ∨ ⟦ env ⊢ q ⟧'
⟦ env ⊢ Imp p q ⟧'   = ⟦ env ⊢ p ⟧' ⇒ ⟦ env ⊢ q ⟧'
⟦ env ⊢ Atomic n ⟧' with lookup n env
... | true  = true
... | false = false

⟦_⊢_⟧ : {n : ℕ} → Env n → BoolExpr n → Set
⟦ env ⊢ p ⟧ = ⟦ env ⊢ p ⟧' ≡ true


-- decision procedure:
-- return whether the given proposition is true
-- this is like our isEvenQ
decide : ∀ {n : ℕ} (e : Env n) → BoolExpr n → Bool
decide env (Truth)      = true
decide env (Falsehood)  = false
decide env (And be be₁) = decide env be ∧ decide env be₁
decide env (Or be be₁)  = decide env be ∨ decide env be₁
decide env (Imp p q)    = ¬ (decide env p) ∨ (decide env q)
decide env (Atomic n)   = lookup n env


mutual
  -- first a helper for the cases where a proposition isn't true
  soundness' : {n : ℕ} → (env : Env n) → (p : BoolExpr n) → decide env p ≡ false → ⟦ env ⊢ p ⟧ → ⊥
  soundness' env Truth () pf
  soundness' env Falsehood dec  pf = {!!}
  soundness' env (And p q) dec pf  = {!!} -- with and-false (decide env p) (decide env q) dec
  -- soundness' env (And p q) dec (proj₁ , proj₂) | inj₁ x = soundness' env p x proj₁
  -- soundness' env (And p q) dec (proj₁ , proj₂) | inj₂ y = soundness' env q y proj₂
  soundness' env (Or p q) dec  pf  = {!!} -- with or-false (decide env p) (decide env q) dec
  -- soundness' env (Or p q) dec (inj₁ x) | proj₁ , proj₂ = soundness' env p proj₁ x
  -- soundness' env (Or p q) dec (inj₂ y) | proj₁ , proj₂ = soundness' env q proj₂ y
  soundness' env (Imp p q) dec pf  with or-false (¬ (decide env p)) (decide env q) dec
  soundness' env (Imp p q) dec pf | proj₁ , proj₂  with not-false proj₁
  ... | tmppat  = {!!} -- with pf (soundness env p tmppat)
  -- ... | tmppatq = soundness' env q proj₂ tmppatq
  soundness' env (Atomic x) dec pf  with lookup x env
  soundness' env (Atomic x) ()  pf | true
  soundness' env (Atomic x) dec pf | false = {!!}

  -- soundness theorem:
  soundness : {n : ℕ} → (env : Env n) → (p : BoolExpr n) → decide env p ≡ true → ⟦ env ⊢ p ⟧
  soundness env (Truth) refl = {!!}
  soundness env (Falsehood) ()
  soundness env (And p p₁) pf = {!!} -- (soundness env p  (and-l pf)) ,
                                  -- (soundness env p₁ (and-r (decide env p) (decide env p₁) pf))
  soundness env (Or p p₁) pf  with or-lem (decide env p) (decide env p₁) pf
  soundness env (Or p p₁) pf | inj₁ x = {!!} -- inj₁ (soundness env p x)
  soundness env (Or p p₁) pf | inj₂ y = {!!} -- inj₂ (soundness env p₁ y)
  soundness env (Imp p q) pf  with or-lem (¬ (decide env p)) (decide env q) pf
  soundness env (Imp p q) pf | inj₁ y = {!!} -- λ x → ⊥-elim (soundness' env p (not-lemma y) x)
  soundness env (Imp p q) pf | inj₂ y = {!!} -- λ x → soundness env q y
  soundness env (Atomic n) pf with lookup n env
  soundness env (Atomic n₁) refl | .true = {!!} 


-- still required:
-- * do actual reflection

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
    thm0 : ∀ (ov : Env 1) → ⟦ ov ⊢ Or (Atomic zero) (Imp (Falsehood) (Atomic zero))⟧
    thm0 (true ∷ [])  = soundness (true ∷ [])  (Or (Atomic zero) (Imp Falsehood (Atomic zero))) refl
    thm0 (false ∷ []) = soundness (false ∷ []) (Or (Atomic zero) (Imp Falsehood (Atomic zero))) refl

    thm1 : ∀ (ov : Env 1) → ⟦ ov ⊢ Imp (Atomic zero) (Atomic zero) ⟧
    --thm1 ov = soundness ov (Imp (Atomic zero) (Atomic zero)) refl
    thm1 (true ∷ [])  = soundness (true ∷ [])  (Imp (Atomic zero) (Atomic zero)) refl
    thm1 (false ∷ []) = soundness (false ∷ []) (Imp (Atomic zero) (Atomic zero)) refl

-- next step: try and avoid having to enumerate all the possible environments,
-- as this will quickly become tedious (and remember, the challenge was to
-- prove tautologies in n² and not 2ⁿ with n the number of variables...


-- TODO write a version which returns a
-- proof either way, not a maybe. possibly using a predicate to be instantiated
-- to refl?
automate : ∀ (n : ℕ) (env : Env n) (p : BoolExpr n) → Maybe ⟦ env ⊢ p ⟧
automate n env p  with decide env p | inspect (decide env) p
automate n env p | true  | by eq = just (soundness env p eq)
automate n env p | false | by eq = nothing

private
  thm2 : ∀ (ov : Env 1) → ⟦ ov ⊢ Or (Atomic zero) (Imp Falsehood (Atomic zero))⟧
  thm2 ov  with automate 1 ov (Or (Atomic zero) (Imp Falsehood (Atomic zero)))
  thm2 ov | just x = x
  thm2 ov | nothing = {!!}

  thm3 : ∀ (ov : Env 1) → ⟦ ov ⊢ Imp (Atomic zero) (Atomic zero) ⟧
  thm3 ov  with automate 1 ov (Imp (Atomic zero) (Atomic zero))
  thm3 ov | just x = x
  thm3 ov | nothing = {!!}

  o  : Fin 4
  o  = suc zero
  t  : Fin 4
  t  = suc (suc zero)
  th : Fin 4
  th = suc (suc (suc zero))

  -- this means the following: ((p1 ∨ q1) ∧ (p2 ∨ q2) → (q1 ∨ p1) ∧ (q2 ∨ p2))
  -- ...which is cool, since we can now prove tautologies of this form.
  thm1bdef : BoolExpr 4
  thm1bdef = Imp (And (Or (Atomic zero) (Atomic t)) (Or (Atomic o) (Atomic th)))
                 (And (Or (Atomic t) (Atomic zero)) (Or (Atomic th) (Atomic o)))

  thm1b : ∀ (ov : Env 4) → ⟦ ov ⊢ thm1bdef ⟧
  thm1b ov with automate 4 ov thm1bdef
  thm1b ov | just x = x
  thm1b ov | nothing = {!!} -- we want absurd here.

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
term2b : (n : ℕ) → (depth : ℕ) → (t : Term) → isBoolExprQ (argsNo t) 0 t ≡ true → (BoolExpr n)
term2b n depth t pf with stripPi t
term2b n depth t pf | var x args with suc (unsafeMinus x depth) ≤? n
term2b n depth t pf | var x args | yes p2 = Atomic (fromℕ≤ {unsafeMinus x depth} p2)
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

  -- here we'll test the reflection a bit
  -- sort of like a few unit tests...

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

-- this should be an fmap.
-- subst : {n : ℕ} → (var : ℕ) → (t : Set) → BoolExpr n → BoolExpr n
-- subst v t Truth              = Truth
-- subst v t Falsehood          = Falsehood
-- subst v t (And exp exp₁)     = And (subst v t exp) (subst v t exp₁)
-- subst v t (Or exp exp₁)      = Or (subst v t exp) (subst v t exp₁)
-- subst v t (Imp exp exp₁)     = Imp (subst v t exp) (subst v t exp₁)
-- subst v t (Atomic x) with Data.Nat._≟_ (toℕ x) v
-- subst v t (Atomic x) | yes p = SET t
-- subst v t (Atomic x) | no ¬p = Atomic x
-- subst v t (SET a)            = SET a

isSubstituted : {n : ℕ} → (b : BoolExpr n) → Bool
isSubstituted (Atomic x) = false
isSubstituted Truth      = true
isSubstituted Falsehood  = true
isSubstituted (And b b₁) = isSubstituted b ∧ isSubstituted b₁
isSubstituted (Or b b₁)  = isSubstituted b ∧ isSubstituted b₁
isSubstituted (Imp b b₁) = isSubstituted b ∧ isSubstituted b₁

-- ⟦_⟧ : Substituted → Set
-- ⟦ STruth ⟧      = ⊤
-- ⟦ SFalsehood ⟧  = ⊥
-- ⟦ SAnd b b₁ ⟧   = ⟦ b ⟧ × ⟦ b₁ ⟧
-- ⟦ SOr b b₁ ⟧    = ⟦ b ⟧ ⊎ ⟦ b₁ ⟧
-- ⟦ SImp b b₁ ⟧   = ⟦ b ⟧ → ⟦ b₁ ⟧
-- ⟦ SSET a ⟧      = a

-- be2substituted : (b : BoolExpr zero) → Substituted
-- be2substituted Truth      = STruth
-- be2substituted Falsehood  = SFalsehood
-- be2substituted (And b b₁) = SAnd (be2substituted b)
--                                  (be2substituted b₁)
-- be2substituted (Or b b₁)  = SOr  (be2substituted b)
--                                  (be2substituted b₁)
-- be2substituted (Imp b b₁) = SImp (be2substituted b)
--                                  (be2substituted b₁)
-- be2substituted (SET a)    = SSET a
-- be2substituted (Atomic ()) 

toZero : {n : ℕ} → (b : BoolExpr n) → isSubstituted b ≡ true → BoolExpr zero
toZero {zero}  x          pf = x         -- verbose identity.
toZero {suc n} Truth      pf = Truth     -- verbose casting.
toZero {suc n} Falsehood  pf = Falsehood
toZero {suc n} (And x x₁) pf = And (toZero x (and-l pf))
                                   (toZero x₁ (and-r (isSubstituted x) (isSubstituted x₁) pf) )
toZero {suc n} (Or x x₁)  pf = Or  (toZero x (and-l pf))
                                   (toZero x₁ (and-r (isSubstituted x) (isSubstituted x₁) pf) )
toZero {suc n} (Imp x x₁) pf = Imp (toZero x (and-l pf))
                                   (toZero x₁ (and-r (isSubstituted x) (isSubstituted x₁) pf))
toZero {suc n} (Atomic x) ()

freeVars : {n : ℕ} → BoolExpr n → ℕ
freeVars Truth = 0
freeVars Falsehood = 0
freeVars (And x x₁) = (freeVars x) + (freeVars x₁)
freeVars (Or x x₁) = (freeVars x) + (freeVars x₁)
freeVars (Imp x x₁) = (freeVars x) + (freeVars x₁)
freeVars (Atomic x) = 1

noFree⇒isSubstituted : {n : ℕ} → (x : BoolExpr n) → freeVars x ≡ zero → isSubstituted x ≡ true
noFree⇒isSubstituted Truth pf = refl
noFree⇒isSubstituted Falsehood pf = refl
noFree⇒isSubstituted (And x x₁) pf = {!!}
noFree⇒isSubstituted (Or x x₁) pf = {!!}
noFree⇒isSubstituted (Imp x x₁) pf = {!!}
noFree⇒isSubstituted (Atomic x) pf = {!!}

{-
TODO:

- enforce that the environments are what you'd expect (i.e. prepend false right, true left,
  when building up tree
-
-}
data Tree {n : ℕ} (b : BoolExpr n) : (depth : ℕ) → (height : ℕ) → Set where
  Node : {depth h : ℕ}
       → (l : Tree b (suc depth) h)
       → (r : Tree b (suc depth) h) → Tree b depth (suc h)
  Leaf : (env : Env n) → decide env b ≡ true → Tree b n 0
  
-- adds a telescope type with the right number of free variables
-- to a type/proposition.
-- telescope : {n : ℕ} → (freevars : ℕ) → BoolExpr n → Set
-- telescope (suc n) x = (b : Set) → telescope n ( subst n b x ) -- TODO check n is right. maybe we need (degree b - n)
-- telescope zero x    = ⟦ stdtd ⟧
--   where stdtd  = be2substituted (toZero x (noFree⇒isSubstituted x {!refl!}))

-- here P is some predicate which should hold for an environment.
forallEnvs : (n : ℕ) → (P : Env n → Set) → Set
forallEnvs zero    p = p []
forallEnvs (suc n) p = (forallEnvs n (λ env → p (true ∷ env))) × (forallEnvs n (λ env → p (false ∷ env)))

-- foo shows us that, if we have that some P holds for all envs,
-- we can find the corresponding proof if given some specific env.
foo : {n : ℕ} → (env : Env n) → (P : Env n → Set) → forallEnvs n P → P env
foo []          pred pf              = pf
foo (true ∷ p)  pred (proj₁ , proj₂) = foo p (λ z → pred (true ∷ z))  proj₁
foo (false ∷ p) pred (proj₁ , proj₂) = foo p (λ z → pred (false ∷ z)) proj₂



-- allEnvs : (n : ℕ) → Tree (Env n)
-- allEnvs zero    = Leaf []
-- allEnvs (suc n) = Node ( (allEnvs n)) -- false branch?
--                        ( (allEnvs n)) -- true branch?

-- this checks, by brute force, if an expression is a tautology,
-- that is, if it's true for all possible variable assignments.
-- this would be where to implement a smarter solver.
decideForallEnv : {n : ℕ} → BoolExpr n → Bool
decideForallEnv {n} exp = {!!} -- (allEnvs n)

exp0 : BoolExpr 0
exp0 = Imp Truth Truth

test00 : Tree exp0 0 0
test00 = Leaf [] refl

exp1 : BoolExpr 1
exp1 = Imp (Atomic zero) (Atomic zero)

test : Tree exp1 0 1
test = Node (Leaf (true ∷ []) refl) {!Leaf (false ∷ []) refl!}

findInTree : {m : ℕ} → (b : BoolExpr m) → Tree b 0 m → (∀ env → ⟦ env ⊢ b ⟧)
findInTree expr t    = {!!} 

-- generalises : {n : ℕ} → (b : BoolExpr n) → (∀ env → ⟦ env ⊢ b ⟧) → telescope n b
-- generalises lk = {!!}

-- decideforallenv ==true -> forallenvs??

-- allTrue→elemTrue : (l : List Bool) → allTrue l ≡ true → x ≡ true -- forall x ∈ l
-- allTrue→elemTrue l x p = ?

unfoldTruth : {as : List Bool} {a : Bool} → foldr _∧_ true (a ∷ as) ≡ true → foldr _∧_ true as ≡ true
unfoldTruth {as} {a} x = and-r a (foldr _∧_ true as) x

s : {n : ℕ} → (p : BoolExpr n) → decideForallEnv p ≡ true → forallEnvs n (λ env → decide env p ≡ true)
s {zero}  x  dec = {!!}
s {suc n} Truth dec = {!!}
s {suc n} Falsehood dec = {!!}
s {suc n} (And exp exp₁) dec = {!!}
s {suc n} (Or exp exp₁) dec = {!!}
s {suc n} (Imp exp exp₁) dec = {!!}
s {suc n} (Atomic x) dec = {! !}

-- this is actually our soundness function.
-- automate2 : {n : ℕ} → (p : BoolExpr n) → forallEnvs n (λ env → decide env p ≡ true) → telescope n p
-- --automate2 : {n : ℕ} → (p : BoolExpr n) → decideForallEnv p ≡ true → telescope n p
-- automate2 {zero} x pfunc = s {!!} pfunc
-- automate2 {suc n} x pfunc = {!!}

somethm : Set
somethm = (b c : Bool) → (b ⇒ b ∨ true) ∧ (c ∨ ¬ c) ≡ true

goalbla : somethm
goalbla = quoteGoal e in {!!} -- automate2 (term2b (argsNo e) 0 (stripPi e) ?) {!!}

goalbla2 : myfavouritetheorem
goalbla2 = quoteGoal e in {!!}

-- next up!! using foo, find forallEnvs n (\ e -> [[ b ]] e)
-- possible using Tree.
