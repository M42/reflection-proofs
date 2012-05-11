{-# OPTIONS --type-in-type #-}
module Bool where

open import Relation.Binary.PropositionalEquality renaming ( [_] to by ; subst to substpe)
open import Data.Bool renaming (_∧_ to _b∧_ ; _∨_ to _b∨_; not to bnot)
open import Data.Nat
open import Data.Fin hiding (_+_; pred)
open import Data.Vec renaming (reverse to vreverse)
open import Data.Unit hiding (_≤?_)
open import Data.Empty
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.List hiding (_++_; map)

-- first we define a few aliases, to make types look
-- like propositions
¬_ : Set → Set
¬_ = λ x → (⊥ → x)

_∧_ : Set → Set → Set
_∧_ = _×_

_∨_ : Set → Set → Set
_∨_ = _⊎_

-- here's an example of a manual proof
trueandtrue : ⊤ ∧ ⊤ → ⊤
trueandtrue (tt , tt) = tt
-- wouldn't it be nice if we could automate this?

-- eventually we'd like to prove these kinds of tautologies:
myfavouritetheorem : Set
myfavouritetheorem = (p1 q1 p2 q2 : Set) → (p1 ∨ q1) ∧ (p2 ∨ q2)
                                         → (q1 ∨ p1) ∧ (q2 ∨ p2)

proof1 : myfavouritetheorem
proof1 = {! refl!}   -- this won't work, since p1 != q1, etc
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
  SET       : {n : ℕ} → (a : Set)               → BoolExpr n

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
⟦ env ⊢ SET a ⟧     = a



-- decision procedure:
-- return whether the given proposition is true
-- this is like our isEvenQ
decide : ∀ {n : ℕ} (e : Env n) → BoolExpr n → Bool
decide env (Truth)      = true
decide env (Falsehood)  = false
decide env (And be be₁) = decide env be b∧ decide env be₁
decide env (Or be be₁)  = decide env be b∨ decide env be₁
decide env (Imp p q)    = bnot (decide env p) b∨ (decide env q)
decide env (Atomic n)   = lookup n env
decide env (SET a)      = {!!} -- should prevent this with some predicate?

open import Lemmas

mutual
  -- first a helper for the cases where a proposition isn't true
  soundness' : {n : ℕ} → (env : Env n) → (p : BoolExpr n) → decide env p ≡ false → ⟦ env ⊢ p ⟧ → ⊥
  soundness' env Truth () pf
  soundness' env Falsehood dec  pf = pf
  soundness' env (And p q) dec pf  with and-false (decide env p) (decide env q) dec
  soundness' env (And p q) dec (proj₁ , proj₂) | inj₁ x = soundness' env p x proj₁
  soundness' env (And p q) dec (proj₁ , proj₂) | inj₂ y = soundness' env q y proj₂
  soundness' env (Or p q) dec  pf  with or-false (decide env p) (decide env q) dec
  soundness' env (Or p q) dec (inj₁ x) | proj₁ , proj₂ = soundness' env p proj₁ x
  soundness' env (Or p q) dec (inj₂ y) | proj₁ , proj₂ = soundness' env q proj₂ y
  soundness' env (Imp p q) dec pf  with or-false (bnot (decide env p)) (decide env q) dec
  soundness' env (Imp p q) dec pf | proj₁ , proj₂  with not-false proj₁
  ... | tmppat  with pf (soundness env p tmppat)
  ... | tmppatq = soundness' env q proj₂ tmppatq
  soundness' env (Atomic x) dec pf  with lookup x env
  soundness' env (Atomic x) ()  pf | true
  soundness' env (Atomic x) dec pf | false = pf
  soundness' env (SET a)    dec pf = {!!}

  -- soundness theorem:
  soundness : {n : ℕ} → (env : Env n) → (p : BoolExpr n) → decide env p ≡ true → ⟦ env ⊢ p ⟧
  soundness env (Truth) refl = tt
  soundness env (Falsehood) ()
  soundness env (And p p₁) pf = (soundness env p  (and-l pf)) ,
                                (soundness env p₁ (and-r (decide env p) (decide env p₁) pf))
  soundness env (Or p p₁) pf  with or-lem (decide env p) (decide env p₁) pf
  soundness env (Or p p₁) pf | inj₁ x = inj₁ (soundness env p x)
  soundness env (Or p p₁) pf | inj₂ y = inj₂ (soundness env p₁ y)
  soundness env (Imp p q) pf  with or-lem (bnot (decide env p)) (decide env q) pf
  soundness env (Imp p q) pf | inj₁ y = λ x → ⊥-elim (soundness' env p (not-lemma y) x)
  soundness env (Imp p q) pf | inj₂ y = λ x → soundness env q y
  soundness env (Atomic n) pf with lookup n env
  soundness env (Atomic n₁) refl | .true = tt
  soundness env (SET a)   pf = {!!}

open import Data.Nat
open import Relation.Nullary hiding (¬_)
open import Data.Product hiding (map)

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
    thm0 (true ∷ [])  = soundness (true ∷ []) (Or (Atomic zero) (Imp Falsehood (Atomic zero))) refl
    thm0 (false ∷ []) = soundness (false ∷ []) (Or (Atomic zero) (Imp Falsehood (Atomic zero))) refl

    thm1 : ∀ (ov : Env 1) → ⟦ ov ⊢ Imp (Atomic zero) (Atomic zero) ⟧
    --thm1 ov = soundness ov (Imp (Atomic zero) (Atomic zero)) refl
    thm1 (true ∷ []) = soundness (true ∷ []) (Imp (Atomic zero) (Atomic zero)) refl
    thm1 (false ∷ []) = soundness (false ∷ []) (Imp (Atomic zero) (Atomic zero)) refl

-- next step: try and avoid having to enumerate all the possible environments,
-- as this will quickly become tedious (and remember, the challenge was to
-- prove tautologies in n² and not 2ⁿ with n the number of variables...

open import Data.Maybe hiding (Eq)

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

open import Data.Vec.Properties
open import Data.Nat.Properties
open ≡-Reasoning

open import Relation.Binary

-- okay, next attempt: using quoteGoal

open import Reflection

≡' : Name
≡' = quote _≡_

-- returns the number of the outermost pi quantified variables.

argsNo : Term → ℕ
argsNo (pi (arg visible relevant (el (lit 0) (sort (lit 0)))) (el s t)) = suc (argsNo t)
-- argsNo (pi (arg visible relevant (el (lit 0) (def  _ _))) (el s t)) = suc (argsNo t)
argsNo (var x args) = 0
argsNo (con c args) = 0
argsNo (def f args) = 0
argsNo (lam v t) = 0
argsNo (sort x) = 0
argsNo unknown = 0
argsNo _ = 0

-- peels off all the outermost Pi constructors,
-- returning a term with argsNo free variables.

stripPi : Term → Term
stripPi (pi (arg visible relevant (el (lit 0) (sort (lit 0)))) (el s t)) = stripPi t
--stripPi (pi (arg visible relevant (el (lit 0) (def  _ _))) (el s t)) = stripPi t
-- identity otherwise
stripPi (pi args t) = pi args t
stripPi (var x args) = var x args
stripPi (con c args) = con c args
stripPi (def f args) = def f args
stripPi (lam v t) = lam v t
stripPi (sort x) = sort x
stripPi unknown = unknown

isTrue  : (c : Name) (args : List (Arg Term)) → Bool
isFalse : (c : Name) (args : List (Arg Term)) → Bool
isAnd   : (f : Name) (args : List (Arg Term)) → Bool
isOr    : (f : Name) (args : List (Arg Term)) → Bool
isNot   : (f : Name) (args : List (Arg Term)) → Bool

isName : Name → Name → List (Arg Term) → Bool
isName cc f args with f ≟-Name cc | args
isName cc f args | yes p | _ = true
isName cc f args | no ¬p | _ = false

lengthis : {a : Set} → List a → ℕ → Bool
lengthis []        zero    = true
lengthis (_ ∷ lst) (suc n) = lengthis lst n
lengthis  _        _       = false

isTrue  c as = isName (quote ⊤) c as     b∧ lengthis as 0
isFalse c as = isName (quote ⊥) c as     b∧ lengthis as 0
isAnd   c as = isName (quote _∧_) c as   b∧ lengthis as 2
isOr    c as = isName (quote _∨_) c as   b∧ lengthis as 2
isNot   c as = isName (quote ¬_) c as    b∧ lengthis as 1

allTrue : {n : ℕ} → Vec Bool n → Bool
allTrue {zero}  = λ _ → true
allTrue {suc n} = foldr₁ _b∧_

mutual
  isBoolArg : {n : ℕ} → Arg Term → Bool
  isBoolArg {n} (arg v r x) = isBoolExpr {n} x

  isBoolExpr : {n : ℕ} → Term → Bool
  isBoolExpr {n} (var x args) with suc x ≤? n
  ... | yes p = true
  ... | no ¬p = false
  isBoolExpr {n} (con c args) = (isTrue c args
                          b∨ isFalse c args)
                          b∧ allTrue (map (isBoolArg {n}) (fromList args))
  isBoolExpr {n} (def f args) = (isAnd f args
                          b∨ isOr f args
                          b∨ isNot f args)
                          b∧ allTrue (map (isBoolArg {n}) (fromList args))
  isBoolExpr (lam v t)    = false
  isBoolExpr (pi t₁ t₂)   = false
  isBoolExpr (sort x)     = false
  isBoolExpr unknown      = false

someThm : ∀ {p1 p2 q1 q2} → ((p1 ∨ q1) ∧ (p2 ∨ q2)) → ((q1 ∨ p1) ∧ (q2 ∨ p2))
someThm = quoteGoal g in {! (lhs g refl)!} -- C-c C-n in this goal is useful.

argsAreExpressions : {n : ℕ} {a : Term} {p₁ p₃ : Bool} →
                     p₁ b∧ (
                     isBoolExpr {n} a
                     ) b∧ p₃ ≡ true →
                     isBoolExpr {n} a ≡ true
argsAreExpressions pf = {!!}
argsAreExpressions₂ : {n : ℕ} {a : Term} {p₁ p₂ p₄ : Bool} →
                     p₁ b∧ p₂ b∧ (
                     isBoolExpr {n} a
                     ) b∧ p₄ ≡ true →
                     isBoolExpr {n} a ≡ true
argsAreExpressions₂ pf = {!!}


-- this should take a LHS or RHS and turn it into
-- something in our AST language
term2boolexpr : {n : ℕ} → (t : Term) →
            isBoolExpr {n} t ≡ true  →
            BoolExpr n
term2boolexpr {n} (var x args) eq with suc x ≤? n
term2boolexpr (var x args) eq | yes p = Atomic (fromℕ≤ p)
term2boolexpr (var x args) () | no ¬p
term2boolexpr (con c args) isBE with c ≟-Name (quote ⊤)
... | yes _ = Truth
... | no _ with c ≟-Name (quote ⊥)
... | yes _ = Falsehood
term2boolexpr (con c args) () | no _ | no _ -- we only know true and false as constructors.
term2boolexpr (def f as) isBE with f ≟-Name (quote _∧_) -- is it an and?
term2boolexpr (def f []) () | yes  _
term2boolexpr (def f (arg _ _ a₁ ∷ [])) () | yes  _
term2boolexpr {n} (def f (arg _ _ a₁ ∷ arg _ _ a₂ ∷ l)) isBE | yes p = And (term2boolexpr a₁ (argsAreExpressions {n} isBE))
                                                                   (term2boolexpr a₂ (argsAreExpressions₂ {n} isBE))
... | no _ with f ≟-Name (quote _∨_) -- or maybe an or?
term2boolexpr {n} (def f (arg _ _ a₁ ∷ arg _ _ a₂ ∷ l)) isBE | no _ | yes p = Or (term2boolexpr a₁ (argsAreExpressions {n} isBE))
                                                                         (term2boolexpr a₂ (argsAreExpressions₂ {n} isBE))
term2boolexpr (def f l) () | no _ | yes p
term2boolexpr (def f as) pf | no _ | no _ with f ≟-Name (quote ¬_)
... | no _ = {!!}
term2boolexpr {n} (def f (arg _ _ a₁ ∷ l)) isBE | no _ | no _ | yes p = Imp Falsehood (term2boolexpr a₁ (argsAreExpressions {n} isBE))
term2boolexpr (def f l) () | no _ | no _ | yes _
term2boolexpr (lam v t)    ()
term2boolexpr (pi t₁ t₂)   ()
term2boolexpr (sort x)     ()
term2boolexpr unknown      ()

open import Data.Vec.N-ary

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

-- we don't have a branch for Not, since that is immediately
-- translated as "¬ P ⇒ λ ⊥ → P"
term2b : (n : ℕ) → (depth : ℕ) → (t : Term) → (BoolExpr n)
term2b n depth t with stripPi t
term2b n depth t | var x args with suc (unsafeMinus x depth) ≤? n
term2b n depth t | var x args | yes p2 = Atomic (fromℕ≤ {unsafeMinus x depth} p2)
term2b n depth t | var x args | _      = Falsehood --warning
term2b n depth t | con c args = {!!}
term2b n depth t | def f args with f ≟-Name (quote Data.Product.Σ)
term2b n depth t | def f (_ ∷ _ ∷ arg _ _ t₁ ∷ arg _ _ t₂ ∷ []) | yes p = And (term2b n depth t₁) (term2b n depth t₂)
term2b n depth t | def f (_) | yes p = Falsehood -- wrong arguments for And
term2b n depth t | def f args | no p  with f ≟-Name (quote Data.Empty.⊥)
term2b n depth t | def f []   | no _ | yes p = Falsehood -- bonafide
term2b n depth t | def f args | no _ | yes p = {!!}
term2b n depth t | def f args | no _ | no  p with f ≟-Name (quote Data.Sum._⊎_)
term2b n depth t | def f (_ ∷ _ ∷ arg _ _ t₁ ∷ arg _ _ t₂ ∷ []) | no _ | no _ | yes p = Or (term2b n depth t₁)
                                                                                           (term2b n depth t₂)
term2b n depth t | def f args | no _ | no _ | yes _  = Falsehood --warning
term2b n depth t | def f args | no _ | no _ | no _ with f ≟-Name (quote Data.Unit.⊤)
term2b n depth t | def f [] | no _   | no _    | no _    | yes _ = Truth
term2b n depth t | def f _ | no _   | no _    | no _    | yes _ = Falsehood -- warning
term2b n depth t | def f _  | no _   | no _    | no _    | no _ = Falsehood -- warning

term2b n depth t | lam v t' = term2b n (suc depth) t'
term2b n depth t | pi (arg visible relevant (el _ t₁)) (el _ t₂) = Imp (term2b n depth t₁) (term2b n (suc depth) t₂)
term2b n depth t | sort x = Falsehood   -- warning
term2b n depth t | unknown = Falsehood   -- warning
term2b n depth t | _ = Falsehood   -- warning

private
  -- here we'll test the reflection a bit
  -- sort of like a few unit tests...
  test0 : Set
  test0 = (a b c d : Set) → a ∧ b

  test0-check : let t = quoteTerm test0 in
                term2b (argsNo t) 0 t ≡ And (Atomic (suc (suc (suc zero)))) (Atomic (suc (suc zero)))
  test0-check = refl
  test1-check : let t = quoteTerm ( (a b d : Set) → a → b) in
                term2b (argsNo t) 0 t ≡ Imp (Atomic ((suc (suc zero)))) (Atomic ((suc zero)))
  test1-check = refl
  test2-check : let t = quoteTerm ( (a b c : Set) → a ∧ c → b ) in
                term2b (argsNo t) 0 t ≡ Imp (And (Atomic (suc (suc zero))) (Atomic zero)) (Atomic (suc zero))
  test2-check = refl
  test3-check : let t = quoteTerm ( (a b c d : Set) → ¬ a → b ) in
                term2b (argsNo t) 0 t ≡ Imp (Imp Falsehood (Atomic (suc (suc (suc zero))))) (Atomic (suc (suc zero)))
  test3-check = refl
  test4-check : let t = quoteTerm ( (a b c d : Set) → ⊥ ∨ b ) in
                term2b (argsNo t) 0 t ≡ Or (Falsehood) (Atomic (suc (suc zero)))
  test4-check = refl


forallenvs : ∀ (n : ℕ)  (e : Env n) → (b : BoolExpr n) → decide e b ≡ true → ⟦ e ⊢ b ⟧
forallenvs = {!!}

-- this should be an fmap.
subst : {n : ℕ} → (var : ℕ) → (t : Set) → BoolExpr n → BoolExpr n
subst v t Truth = Truth
subst v t Falsehood = Falsehood
subst v t (And exp exp₁) = And (subst v t exp) (subst v t exp₁)
subst v t (Or exp exp₁) = Or (subst v t exp) (subst v t exp₁)
subst v t (Imp exp exp₁) = Imp (subst v t exp) (subst v t exp₁)
subst v t (Atomic x) with Data.Nat._≟_ (toℕ x) v
subst v t (Atomic x) | yes p = SET t
subst v t (Atomic x) | no ¬p = Atomic x
subst v t (SET a) = SET a


_⟦_⟧ : {n : ℕ} → (freeVars : ℕ) → (b : BoolExpr n) →  -- something
                Set
suc n ⟦ x ⟧ = (b : Set) → n ⟦ subst n b x ⟧ -- hoping this'll introduce a fresh variable? TODO check n is right. maybe we need (degree b - n)
zero ⟦ Truth ⟧ = ⊤
zero ⟦ Falsehood ⟧ = ⊥
zero ⟦ And b b₁ ⟧ = (zero ⟦ b ⟧) × (zero ⟦ b₁ ⟧)
zero ⟦ Or b b₁ ⟧ = (zero ⟦ b ⟧) ⊎ (zero ⟦ b₁ ⟧)
zero ⟦ Imp b b₁ ⟧ = zero ⟦ b ⟧ → zero ⟦ b₁ ⟧
zero ⟦ SET a ⟧ = a
zero ⟦ Atomic x ⟧ = {!!} -- we must make this absurd.

data Tree : ℕ → Set where
  Nil : Tree zero
  P   : {n : ℕ} → Tree n → Tree n → Tree (suc n) -- pair
  
-- enumerate all the possible envs of a particular size.
allEnvs : (n : ℕ) → Tree n
allEnvs zero    = Nil
allEnvs (suc n) = P (allEnvs n) (allEnvs n)

-- this checks, by brute force, if an expression is a tautology,
-- that is, if it's true for all possible variable assignments.
-- this would be where to implement a smarter solver.
-- decideForallEnv : {n : ℕ} → BoolExpr n → Bool
-- decideForallEnv {n} exp = allTrue (map (λ env → decide env exp) (allEnvs n))


-- -- this is actually our soundness function.
-- automate2 : {n : ℕ} → (p : BoolExpr n) → decideForallEnv p ≡ true → n ⟦ p ⟧
-- automate2 Truth pfunc = {!tt!}
-- automate2 Falsehood pfunc = {!!} -- we want absurd here, but you can't match on pfunc
-- automate2 (And p p₁) pfunc = {!!}
-- automate2 (Or p p₁) pfunc = {!!}
-- automate2 (Not p) pfunc = {!!}
-- automate2 (Imp p p₁) pfunc = {!!}
-- automate2 (Atomic x) pfunc = {!!}
-- automate2 (SET a) pfunc = {!!} 
-- 
-- somethm : Set
-- somethm = (b : Set) → ⊤ ∨ b → ⊤
-- 
-- goalbla : somethm
-- goalbla = quoteGoal e in automate2 (term2b (argsNo e) 0 (stripPi e)) refl


