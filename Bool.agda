{-# OPTIONS --type-in-type #-}
module Bool where

open import Relation.Binary.PropositionalEquality renaming ( [_] to by )
open import Data.Bool renaming (_∧_ to _b∧_ ; _∨_ to _b∨_; not to bnot)
open import Data.Nat
open import Data.Fin hiding (_+_; pred)
open import Data.Vec renaming (reverse to vreverse)
open import Data.Unit hiding (_≤?_)
open import Data.Empty
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.List hiding (_++_)

¬_ : Set → Set
¬_ = λ p → ⊥

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
myfavouritetheorem = ∀ {p1 q1 p2 q2} → (p1 ∨ q1) ∧ (p2 ∨ q2) →
                                       (q1 ∨ p1) ∧ (q2 ∨ p2)

proof1 : myfavouritetheorem
proof1 = {! refl!}   -- this won't work, since p1 != q1, etc!
                     -- proving this manually would require 2ⁿ cases...

-- we'll make some DSL into which we're going to translate theorems
-- (which are actually types of functions), and then use reflection
-- in some unmagical way... see below.

data BoolExpr : ℕ → Set where
  Truth     : {n : ℕ}                           → BoolExpr n
  Falsehood : {n : ℕ}                           → BoolExpr n
  And       : {n : ℕ} → BoolExpr n → BoolExpr n → BoolExpr n
  Or        : {n : ℕ} → BoolExpr n → BoolExpr n → BoolExpr n
  Not       : {n : ℕ} → BoolExpr n              → BoolExpr n
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
decide env (And be be₁) = decide env be b∧ decide env be₁
decide env (Or be be₁)  = decide env be b∨ decide env be₁
decide env (Not p)      = bnot (decide env p)
decide env (Imp p q)    = bnot (decide env p) b∨ (decide env q)
decide env (Atomic n)   = lookup n env

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
  soundness' env (Not p) dec   pf = pf (soundness env p (not-false dec))
  soundness' env (Imp p q) dec pf  with or-false (bnot (decide env p)) (decide env q) dec
  soundness' env (Imp p q) dec pf | proj₁ , proj₂  with not-false proj₁
  ... | tmppat  with pf (soundness env p tmppat)
  ... | tmppatq = soundness' env q proj₂ tmppatq
  soundness' env (Atomic x) dec pf  with lookup x env
  soundness' env (Atomic x) ()  pf | true
  soundness' env (Atomic x) dec pf | false = pf

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
    thm0 : ∀ (ov : Env 1) → ⟦ ov ⊢ Or (Atomic zero) (Not (Atomic zero))⟧
    thm0 (true ∷ [])  = soundness (true ∷ []) (Or (Atomic zero) (Not (Atomic zero))) refl
    thm0 (false ∷ []) = soundness (false ∷ []) (Or (Atomic zero) (Not (Atomic zero))) refl

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
  thm2 : ∀ (ov : Env 1) → ⟦ ov ⊢ Or (Atomic zero) (Not (Atomic zero))⟧
  thm2 ov  with automate 1 ov (Or (Atomic zero) (Not (Atomic zero)))
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



------------------------------------------------------------------------

Surj : ∀ {A B}(f : A → B) → Set
Surj f = ∀ y → ∃ λ x → f x ≡ y

Inj : ∀ {A B}(f : A → B) → Set
Inj f = ∀ x₁ x₂ → f x₁ ≡ f x₂ → x₁ ≡ x₂

------------------------------------------------------------------------

isZero : Fin 2 → Bool
isZero zero    = true
isZero (suc _) = false

Surj-isZero : Surj isZero
Surj-isZero true  = zero , refl
Surj-isZero false = suc zero , refl

data Enum (A : Set) : Set where
  surj : (n : ℕ) (f : Fin n → A) → Surj f → Enum A
  inj  : (n : ℕ) (f : A → Fin n) → Inj  f → Enum A

ex₀ : Enum Bool
ex₀ = surj 2 isZero Surj-isZero

------------------------------------------------------------------------

-- integer exponentiation.
_^_ : ℕ → ℕ → ℕ
n ^ zero    = 1
n ^ (suc m) = n * (n ^ m)

blah : {n : ℕ}  → n ≡ Data.Nat._+_ n 0
blah {zero} = refl
blah {suc n} = cong suc blah

open import Data.Vec.Properties
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

sucLem : {n k : ℕ} → suc (n + k) ≡ n + suc k
sucLem {zero} = refl
sucLem {suc n} {k} =  cong suc (sucLem {n} {k })

addlem : {n : ℕ} → suc (n + (1 * n)) ≡ n + (1 * suc n)
addlem {zero} = refl
addlem {suc n} =
  begin
    suc (suc (n + suc (n + zero)))
    ≡⟨ cong suc (cong suc (sym (cong (_+_ n) (cong suc blah)))) ⟩
    suc (suc (n + suc n))
    ≡⟨ cong suc (sucLem {n}) ⟩
    suc (n + suc (suc n))
    ≡⟨ cong suc ( (cong (_+_ n) (cong suc (cong suc blah)))) ⟩
    suc (n + suc (suc (n + zero)))
  ∎

addLists : {n : ℕ} {e : Set}
                     → Vec e n
                     → Vec e n
                     → Vec e (n + n)
addLists l1 l2 = l1 ++ l2

lem₀ : {n m : ℕ} → 2 ^ n + 0 ≡ 2 ^ n
lem₀ {n} {m} = {!!}

-- enumerate all the possible envs of a particular size.
embellish : (n : ℕ) {- → 2 ^ n + 0 ≡ 2 ^ n
                    → 2 ^ n     ≡ 2 ^ n + 0 * 2 ^ n -}
                    → Vec (Env n) (2 ^ n)
embellish zero     = [] ∷ []
embellish (suc n)  = {!!}

-- return the nn'th env with size n
something : ∀ {n : ℕ} → (nn : Fin (2 ^ n)) → Env n
something {n} nn = lookup nn (embellish n)

Surj-something : ∀ {n : ℕ} → Surj (something {n})
Surj-something {n} y = {!!} , {!!}

open import Relation.Binary

_≟-env_ : {n : ℕ} → Decidable {A = Env n} _≡_
_≟-env_ = {!!}

whichElem : {n : ℕ} → (a : Env n) → Vec (Env n) (2 ^ n) → Fin (2 ^ n)
whichElem {zero} [] ([] ∷ []) = zero
whichElem {suc n} elem l = {!l!}

ex₁ : ∀ {n : ℕ} → Enum (Env n)
ex₁ {n} = surj (2 ^ n) something Surj-something

-- okay, next attempt: using quoteGoal

open import Reflection

≡' : Name
≡' = quote _≡_

-- returns the number of the outermost pi quantified variables.

argsNo : Term → ℕ
argsNo (pi t₁ (el s t)) = suc (argsNo t)
argsNo (var x args) = 0
argsNo (con c args) = 0
argsNo (def f args) = 0
argsNo (lam v t) = 0
argsNo (sort x) = 0
argsNo unknown = 0

-- peels off all the outermost Pi constructors,
-- returning a term with argsNo free variables.

stripPi : Term → Term
stripPi (pi t₁ (el s t)) = stripPi t
-- identity otherwise
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

allAnd : List Bool → Bool
allAnd = Data.List.foldr _b∧_ true

mutual
  isBoolArg : {n : ℕ} → Arg Term → Bool
  isBoolArg {n} (arg v r x) = isBoolExpr {n} x

  isBoolExpr : {n : ℕ} → Term → Bool
  isBoolExpr {n} (var x args) with suc x ≤? n
  ... | yes p = true
  ... | no ¬p = false
  isBoolExpr {n} (con c args) = (isTrue c args
                          b∨ isFalse c args)
                          b∧ allAnd (Data.List.map (isBoolArg {n}) args)
  isBoolExpr {n} (def f args) = (isAnd f args
                          b∨ isOr f args
                          b∨ isNot f args)
                          b∧ allAnd (Data.List.map (isBoolArg {n}) args)
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
term2boolexpr {n} (def f (arg _ _ a₁ ∷ l)) isBE | no _ | no _ | yes p = Not (term2boolexpr a₁ (argsAreExpressions {n} isBE))
term2boolexpr (def f l) () | no _ | no _ | yes _
term2boolexpr (lam v t)    ()
term2boolexpr (pi t₁ t₂)   ()
term2boolexpr (sort x)     ()
term2boolexpr unknown      ()

open import Data.Vec.N-ary

-- examples

private
  term-ex : Term
  term-ex = quoteTerm ((n m k : ℕ) → n + m ≡ m + k)

  argsNo-ex : argsNo term-ex ≡ 3
  argsNo-ex = refl

  -- simplefied notation, non-executable
  -- stripPi-ex : stripPi-ex t ≡ def ≡' (var 2 + var 1) ≡ (var 1 + var 0)

-- prove : (t : Term) →
--         let n = argsNo t in
--         let nopi = stripPi t in
--         let env = ? in
--         (eq : isEquality nopi ≡ true) →
--         (lexpr : isBoolExpr (lhs nopi eq) ≡ true) →
--         (rexpr : isBoolExpr (rhs nopi eq) ≡ true) →
--         Eq n _≡_ (curryⁿ ⟦ env ⊢ term2boolexpr (lhs nopi eq) lexpr ⟧) (curryⁿ ⟦ env ⊢ term2boolexpr (rhs nopi eq) rexpr ⟧)
-- prove = {!!}
--


goal2 : ∀ (a b : Set) → (a ∧ b) → (b ∧ a)
goal2 = quoteGoal e in {!e!}

goal₁ : ∀ a b → (a ∧ b → b ∧ a)
goal₁ = quoteGoal e in soundness (true ∷ true ∷ []) {!term2boolexpr (stripPi e) refl!} refl



{-

Thoughts about our workflow. What we'd like to do is the following, given some goal like this:

goal₁ : {a b : Bool} a ∧ b => b ∧ a ≡ true

then using quote:

goal₁ = quoteGoal e in prove e refl*
where refl* means the right number of refl constructors

Since quoteGoal gives us a Term, we'll need some things, such as:

- term2boolexpr : Term → BoolExpr n
- eval : BoolExpr n → NF  (Normal Form)
- checkEqual : NF → NF → Bool

- soundness : checkEqual a b ≡ true → a ≡ b

Which allows us to define:

prove something = left <- lhs something
                  right <- rhs something
                  _ <- isbool left
                  _ <- isbool right
                  normalL <- eval left
                  normalR <- eval right
                  equality <- checkEqual normalL normalR
                  return soundness ... . . . . ?
                  -}

