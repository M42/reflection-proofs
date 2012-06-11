module TautoBoolVariables where

open import Relation.Binary.PropositionalEquality renaming ([_] to by ; subst to substpe)
open import Data.String
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
open import Data.List hiding (_∷ʳ_)

_⇒_ : Bool → Bool → Bool
true  ⇒ true  = true
true  ⇒ false = false
false ⇒ true  = true
false ⇒ false = true

-- inspiration for style of proof
-- or, another one:
bOrNotb : (b : Bool) → b ∨ ¬ b ≡ true
bOrNotb true  = refl
bOrNotb false = refl

bImpb : (b : Bool) → b ⇒ b ≡ true
bImpb true  = refl
bImpb false = refl

-- wouldn't it be nice if we could automate this?

-- eventually we'd like to prove these kinds of tautologies:
myfavouritetheorem : Set
myfavouritetheorem = (p1 q1 p2 q2 : Bool) → (p1 ∨ q1) ∧ (p2 ∨ q2)
                                          ⇒ (q1 ∨ p1) ∧ (q2 ∨ p2)
                                          ≡ true

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

-- decision procedure:
-- return whether the given proposition is true
-- this is like our isEvenQ
decide : ∀ {n : ℕ} (e : Env n) → BoolExpr n → Bool
decide env (Truth)      = true
decide env (Falsehood)  = false
decide env (And be be₁) = decide env be ∧ decide env be₁
decide env (Or be be₁)  = decide env be ∨ decide env be₁
decide env (Not be)     = ¬ decide env be
decide env (Imp p q)    = ¬ (decide env p ∧ (¬ decide env q))
decide env (Atomic n)   = lookup n env

-- returns the number of the outermost pi quantified variables.

argsNo : Term → ℕ
argsNo (pi (arg visible relevant (el (lit _) (def Bool []))) (el s t)) = suc (argsNo t)
argsNo (pi a b)     = 0
argsNo (var x args) = 0
argsNo (con c args) = 0
argsNo (def f args) = 0
argsNo (lam v t)    = 0
argsNo (sort x)     = 0
argsNo unknown      = 0

-- peels off all the outermost Pi constructors,
-- returning a term with argsNo free variables.

stripPi : Term → Term
stripPi (pi (arg visible relevant (el (lit _) (def Bool []))) (el s t)) = stripPi t
-- identity otherwise
stripPi (pi args t)  = pi   args t
stripPi (var x args) = var  x    args
stripPi (con c args) = con  c    args
stripPi (def f args) = def  f    args
stripPi (lam v t)    = lam  v    t
stripPi (sort x)     = sort x
stripPi unknown      = unknown

-- TODO get rid of this!
unsafeMinus : (a : ℕ) → (b : ℕ) → ℕ
unsafeMinus zero m = zero
unsafeMinus n₁ zero = n₁
unsafeMinus (suc n₁) (suc m) = unsafeMinus n₁ m

outerIsEq : (t : Term) → Bool
outerIsEq (var x args) = false
outerIsEq (con c args) = false
outerIsEq (def f args) with Data.Nat._≟_ (length args) 4
outerIsEq (def f []) | yes ()
outerIsEq (def f (x ∷ [])) | yes ()
outerIsEq (def f (x ∷ x₁ ∷ [])) | yes ()
outerIsEq (def f (x ∷ x₁ ∷ x₂ ∷ [])) | yes ()
outerIsEq (def f (x ∷ x₁ ∷ x₂ ∷ arg v r (var x₃ args) ∷ [])) | yes p = false
outerIsEq (def f (x ∷ x₁ ∷ x₂ ∷ arg v r (con c args) ∷ [])) | yes p with f ≟-Name quote _≡_ | c ≟-Name quote true
outerIsEq (def f (x ∷ x₁ ∷ x₂ ∷ arg v r (con c args) ∷ [])) | yes p₂ | yes p | yes p₁ = true
outerIsEq (def f (x ∷ x₁ ∷ x₂ ∷ arg v r (con c args) ∷ [])) | yes p₁ | yes p | no ¬p = false
outerIsEq (def f (x ∷ x₁ ∷ x₂ ∷ arg v r (con c args) ∷ [])) | yes p | no ¬p  | a = false
outerIsEq (def f (x ∷ x₁ ∷ x₂ ∷ arg v r (def f₁ args) ∷ [])) | yes p = false
outerIsEq (def f (x ∷ x₁ ∷ x₂ ∷ arg v r (lam v₁ x₃) ∷ [])) | yes p = false
outerIsEq (def f (x ∷ x₁ ∷ x₂ ∷ arg v r (pi t₁ t₂) ∷ [])) | yes p = false
outerIsEq (def f (x ∷ x₁ ∷ x₂ ∷ arg v r (sort x₃) ∷ [])) | yes p = false
outerIsEq (def f (x ∷ x₁ ∷ x₂ ∷ arg v r unknown ∷ [])) | yes p = false
outerIsEq (def f (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ args)) | yes ()
outerIsEq (def f args) | no ¬p = false
outerIsEq (lam v t)    = false
outerIsEq (pi t₁ t₂)   = false
outerIsEq (sort x)     = false
outerIsEq unknown      = false

withoutEQ : (t : Term) → outerIsEq t ≡ true → Term
withoutEQ (var x args) ()
withoutEQ (con c args) ()
withoutEQ (def f args) pf with Data.Nat._≟_ (length args) 4
withoutEQ (def f []) pf | yes ()
withoutEQ (def f (x ∷ [])) pf | yes ()
withoutEQ (def f (x ∷ x₁ ∷ [])) pf | yes ()
withoutEQ (def f (x ∷ x₁ ∷ x₂ ∷ [])) pf | yes ()
withoutEQ (def f (x ∷ x₁ ∷ x₂ ∷ arg v r (var x₃ args) ∷ [])) () | yes p
withoutEQ (def f (x ∷ x₁ ∷ x₂ ∷ arg v r (con c args) ∷ [])) pf | yes p with f ≟-Name quote _≡_ | c ≟-Name quote true
withoutEQ (def f (x ∷ x₁ ∷ arg v r x₂ ∷ arg v₁ r₁ (con c args) ∷ [])) pf | yes p₂ | yes p | yes p₁ = x₂
withoutEQ (def f (x ∷ x₁ ∷ x₂ ∷ arg v r (con c args) ∷ [])) ()  | yes p₁ | yes p | no ¬p
withoutEQ (def f (x ∷ x₁ ∷ x₂ ∷ arg v r (con c args) ∷ [])) ()  | yes p | no ¬p | a
withoutEQ (def f (x ∷ x₁ ∷ x₂ ∷ arg v r (def f₁ args) ∷ [])) () | yes p
withoutEQ (def f (x ∷ x₁ ∷ x₂ ∷ arg v r (lam v₁ x₃) ∷ [])) ()   | yes p
withoutEQ (def f (x ∷ x₁ ∷ x₂ ∷ arg v r (pi t₁ t₂) ∷ [])) ()    | yes p
withoutEQ (def f (x ∷ x₁ ∷ x₂ ∷ arg v r (sort x₃) ∷ [])) ()     | yes p
withoutEQ (def f (x ∷ x₁ ∷ x₂ ∷ arg v r unknown ∷ [])) ()       | yes p
withoutEQ (def f (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ args)) pf             | yes ()
withoutEQ (def f args) pf | no ¬p = {!pf!}
withoutEQ (lam v t)    ()
withoutEQ (pi t₁ t₂)   ()
withoutEQ (sort x)     ()
withoutEQ unknown      ()

isBoolExprQ' : (n : ℕ) → (depth : ℕ) → (t : Term) → Bool
isBoolExprQ' n depth (var x args) with suc (unsafeMinus x depth) ≤? n
isBoolExprQ' n depth (var x args) | yes p = true
isBoolExprQ' n depth (var x args) | no ¬p = false
isBoolExprQ' n depth (con tf as) with Data.Nat._≟_ 0 (length as)
isBoolExprQ' n depth (con tf []) | yes pp with tf ≟-Name quote true
isBoolExprQ' n depth (con tf []) | yes pp | yes p = true
isBoolExprQ' n depth (con tf []) | yes pp | no ¬p with tf ≟-Name quote false
isBoolExprQ' n depth (con tf []) | yes pp | no ¬p  | yes p = true
isBoolExprQ' n depth (con tf []) | yes pp | no ¬p₁ | no ¬p = false
isBoolExprQ' n depth (con tf (x ∷ as)) | yes p = false
isBoolExprQ' n depth (con tf as) | no ¬p = false
isBoolExprQ' n depth (def f args) with f ≟-Name quote _∧_
isBoolExprQ' n depth (def f (arg _ _ a ∷ arg _ _ b ∷ [])) | yes p = isBoolExprQ' n depth a ∧ isBoolExprQ' n depth b
isBoolExprQ' n depth (def f a) | yes p = false
isBoolExprQ' n depth (def f args) | no ¬p with f ≟-Name quote _∨_
isBoolExprQ' n depth (def f (arg _ _ a ∷ arg _ _ b ∷ [])) | no ¬p  | yes p = isBoolExprQ' n depth a ∧ isBoolExprQ' n depth b
isBoolExprQ' n depth (def f args) | no ¬p  | yes p = false
isBoolExprQ' n depth (def f args) | no ¬p₁ | no ¬p with f ≟-Name quote _⇒_
isBoolExprQ' n depth (def f (arg _ _ a ∷ arg _ _ b ∷ [])) | no ¬p₁ | no ¬p | yes p = isBoolExprQ' n depth a ∧ isBoolExprQ' n depth b
isBoolExprQ' n depth (def f args) | no ¬p₁ | no ¬p  | yes p = false
isBoolExprQ' n depth (def f args) | no ¬p₂ | no ¬p₁ | no ¬p with f ≟-Name quote ¬_
isBoolExprQ' n depth (def f []) | no ¬p₂ | no ¬p₁ | no ¬p | yes p = false
isBoolExprQ' n depth (def f (arg v r x ∷ [])) | no ¬p₂ | no ¬p₁ | no ¬p | yes p = isBoolExprQ' n depth x
isBoolExprQ' n depth (def f (x ∷ x₁ ∷ args)) | no ¬p₂ | no ¬p₁ | no ¬p | yes p = false 
isBoolExprQ' n depth (def f args) | no ¬p₃ | no ¬p₂ | no ¬p₁ | no ¬p = false
isBoolExprQ' n depth (lam v t) = false
isBoolExprQ' n depth (pi t₁ t₂) = false
isBoolExprQ' n depth (sort y) = false
isBoolExprQ' n depth unknown = false

isBoolExprQ : (n : ℕ) → (depth : ℕ) → (t : Term) → outerIsEq t ≡ true → Bool
isBoolExprQ n depth t pf with withoutEQ t pf
isBoolExprQ n depth t pf | t' = isBoolExprQ' n depth t'

-- the holes here should be absurds, but only Agda>=2.3.1 manages
-- the unification.
term2b' : (n : ℕ)
        → (depth : ℕ)
        → (t : Term)
        → isBoolExprQ' n 0 t ≡ true
        → BoolExpr n
term2b' n depth (var x args) pf with suc (unsafeMinus x depth) ≤? n
term2b' n depth (var x args) pf | yes p = Atomic (fromℕ≤ {unsafeMinus x depth} p)
term2b' n depth (var x args) pf | no ¬p = {!pf!}
term2b' n depth (con tf []) pf with tf ≟-Name quote true
term2b' n depth (con tf []) pf | yes p = Truth
term2b' n depth (con tf []) pf | no ¬p with tf ≟-Name quote false
term2b' n depth (con tf []) pf | no ¬p  | yes p = Falsehood
term2b' n depth (con tf []) () | no ¬p₁ | no ¬p
term2b' n depth (con c args) pf = {!pf!}
term2b' n depth (def f args) pf with f ≟-Name quote _∧_
term2b' n depth (def f (arg _ _ a ∷ arg _ _ b ∷ [])) pf | yes p = And
  (term2b' n depth a (and-l pf))
  (term2b' n depth b (and-r (isBoolExprQ' n 0 a) (isBoolExprQ' n 0 b) pf))
term2b' n depth (def f a) pf | yes p = {! pf !}
term2b' n depth (def f args) pf | no ¬p with f ≟-Name quote _∨_
term2b' n depth (def f (arg _ _ a ∷ arg _ _ b ∷ [])) pf | no ¬p  | yes p = Or
  (term2b' n depth a (and-l pf))
  (term2b' n depth b (and-r (isBoolExprQ' n 0 a) (isBoolExprQ' n 0 b) pf))
term2b' n depth (def f args) pf | no ¬p  | yes p = {! pf !}
term2b' n depth (def f args) pf | no ¬p₁ | no ¬p with f ≟-Name quote _⇒_
term2b' n depth (def f (arg _ _ a ∷ arg _ _ b ∷ [])) pf | no ¬p₁ | no ¬p | yes p = Imp
  (term2b' n depth a (and-l pf))
  (term2b' n depth b (and-r (isBoolExprQ' n 0 a) (isBoolExprQ' n 0 b) pf))
term2b' n depth (def f args) pf | no ¬p₁ | no ¬p  | yes p = {! !}
term2b' n depth (def f args) pf | no ¬p₂ | no ¬p₁ | no ¬p with f ≟-Name quote ¬_
term2b' n depth (def f []) pf | no ¬p₂ | no ¬p₁ | no ¬p | yes p = {!!}
term2b' n depth (def f (arg _ _ x ∷ [])) pf | no ¬p₂ | no ¬p₁ | no ¬p | yes p = Not (term2b' n depth x pf)
term2b' n depth (def f (x ∷ x₁ ∷ args)) pf | no ¬p₂ | no ¬p₁ | no ¬p | yes p = {!!}
term2b' n depth (def f args) pf | no ¬p₃ | no ¬p₂ | no ¬p₁ | no ¬p = {!!}
term2b' n depth (lam v t)  ()
term2b' n depth (pi t₁ t₂) ()
term2b' n depth (sort x)   ()
term2b' n depth unknown    ()

term2b : (n : ℕ)
       → (depth : ℕ)
       → (t : Term)
       → (pf : outerIsEq t ≡ true)
       → isBoolExprQ n 0 t pf ≡ true
       → BoolExpr n
term2b n depth t pf pf2 = term2b' n depth (withoutEQ t pf) pf2

data Diff : ℕ -> ℕ -> Set where
  Base : forall {n} -> Diff n n
  Step : forall {n m} -> Diff (suc n) m -> Diff n m

nForalls : (n m : ℕ) -> Diff n m -> BoolExpr m -> Env n -> Set
nForalls .m m Base b env = decide env b ≡ true
nForalls n m (Step y) b env = (a : Bool) -> nForalls (suc n) m y b (a ∷ env)

zeroId : (n : ℕ) -> n ≡ n + 0
zeroId zero                           = refl
zeroId (suc  n) with n + 0 | zeroId n
zeroId (suc .w)    | w     | refl     = refl

succLemma : (n m : ℕ) -> suc (n + m) ≡ n + suc m
succLemma zero m    = refl
succLemma (suc n) m = cong suc (succLemma n m)

coerceDiff : {n m k : ℕ} -> n ≡ m -> Diff k n -> Diff k m
coerceDiff refl d = d

zero-least : (k n : ℕ) -> Diff k (k + n)
zero-least k zero    = coerceDiff (zeroId k) Base
zero-least k (suc n) = Step (coerceDiff (succLemma k n) (zero-least (suc k) n))

forallBool : (m : ℕ) -> BoolExpr m -> Set
forallBool m b = nForalls zero m (zero-least 0 m) b []

{-
notice that u is automatically instantiated, since
there is only one option, namely tt,tt. this is special and
cool, the type system is doing work for us. Note that this is
because eta-reduction only is done in the type system for records
and not for general data types. possibly the reason is because this is
safe in records because recursion isn't allowed. question for agda-café?
-}
foo' : {u : ⊤ × ⊤} -> ℕ
foo' = 5

foo'' : {u : ⊤ × ⊥} -> ℕ
foo'' = 5

baz : ℕ
baz = foo'

data Error (a : String) : Set where

-- very much like ⊥-elim, but for errors.
Error-elim : ∀ {Whatever : Set} {e : String} → Error e → Whatever
Error-elim ()

So : Bool -> Set
So true  = ⊤
So false = Error "Expression isn't a tautology"

forallsAcc : {n m : ℕ} -> (b : BoolExpr m) -> Env n -> Diff n m -> Set
forallsAcc b' env Base = So (decide env b')
forallsAcc b' env (Step y) = forallsAcc b' (true ∷ env) y × forallsAcc b' (false ∷ env) y

foralls : {n : ℕ} -> (b : BoolExpr n) -> Set
foralls {n} b = forallsAcc b [] (zero-least 0 n)

-- dependently typed If
dif : {P : Bool -> Set} -> (b : Bool) -> P true -> P false -> P b
dif true  t f = t
dif false t f = f

soundnessAcc : {m : ℕ} -> (b : BoolExpr m) ->
               {n : ℕ} -> (env : Env n) -> (d : Diff n m) ->
               forallsAcc b env d ->
               nForalls n m d b env
soundnessAcc bexp env Base H with decide env bexp
soundnessAcc bexp env Base H | true = refl
soundnessAcc bexp env Base H | false = Error-elim H
soundnessAcc {m} bexp {n} env (Step y) H = \a -> dif {\b -> nForalls (suc n) m y bexp (b ∷ env)} a
  (soundnessAcc bexp (true  ∷ env) y (proj₁ H))
  (soundnessAcc bexp (false ∷ env) y (proj₂ H))

soundness : {n : ℕ} -> (b : BoolExpr n) -> {i : foralls b} -> forallBool n b
soundness {n} b {i} = soundnessAcc b [] (zero-least 0 n) i

goalbla  : (b c : Bool) → (b ∨ true) ∧ (c ∨ true) ≡ true
goalbla  = quoteGoal e in soundness (term2b (argsNo e) 0 (stripPi e) refl refl)

goalbla2 : (b : Bool) → b ∨ true ≡ true
goalbla2 = quoteGoal e in soundness (term2b (argsNo e) 0 (stripPi e) refl refl)


goalbla3 : (b : Bool) → true ≡ true
goalbla3 = quoteGoal e in soundness (term2b (argsNo e) 0 (stripPi e) refl refl)

-- problem with Imp?
imp : (b : Bool) → b ∨ ¬ b ≡ true
imp = quoteGoal e in soundness (term2b (argsNo e) 0 (stripPi e) refl refl)

peirce : (p q  : Bool) → (((p ⇒ q) ⇒ p) ⇒ p) ≡ true
peirce = quoteGoal e in {!soundness (term2b (argsNo e) 0 (stripPi e) refl refl)!}


mft : myfavouritetheorem
mft = quoteGoal e in {!!}