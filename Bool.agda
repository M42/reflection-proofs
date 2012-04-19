module Bool where

open import Relation.Binary.PropositionalEquality renaming ( [_] to by )
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
myfavouritetheorem = {p1 q1 p2 q2 : Bool} → ((p1 ∨ q1) ∧ (p2 ∨ q2) ≡
                                             (q1 ∨ p1) ∧ (q2 ∨ p2))
proof1 : myfavouritetheorem
proof1 = {! refl!}   -- this won't work, since p1 != q1, etc!
                     -- proving this manually would require 2ⁿ cases...

-- we'll make some DSL into which we're going to translate theorems
-- (which are actually types of functions), and then use reflection
-- in some magical way... TBC

open import Data.Nat
open import Data.Fin hiding (_+_; pred)

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
open import Data.Sum hiding (map)
open import Data.Product hiding (map)

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
  soundness' env (Imp p q) dec pf  with or-false (not (decide env p)) (decide env q) dec
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

open import Data.Maybe

-- TODO understand this function, and write a version which returns a
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
  t : Fin 4
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
  thm1b ov | nothing = {!!}

-- First: return proof either way, not maybe, from automate,
-- then: prove that you can enumerate all possible Env's and use
-- that to call decide...


open import Data.Unit
open import Relation.Nullary

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

doubleList : {n : ℕ} → Bool → Env n → Env (suc n)
doubleList x env = x ∷ env

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
  
addLists : {n m : ℕ} → suc (n + suc (n + 0)) ≡ suc (suc (n + (n + 0)))
                     → Vec (Env m) n
                     → Vec (Env m) n
                     → Vec (Env m) (2 * n)
addLists {zero}  {zero} _ [] [] = []
addLists {zero}  {m} () l1 l2 
addLists {n} {zero} () l1 l2
addLists {suc n} {suc m} pf (e1 ∷ e2) (e3 ∷ e4) =  {!e1 ∷ e3 ∷ addLists {?} {?} ? e2 e4 !}

-- enumerate all the possible envs of a particular size.
embellish : (n : ℕ) → Vec (Env n) (2 ^ n)
embellish zero = [] ∷ []
embellish (suc n) = addLists ({!!}) (map (doubleList false) (embellish n))
                                           (map (doubleList true)  (embellish n))
                    
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
