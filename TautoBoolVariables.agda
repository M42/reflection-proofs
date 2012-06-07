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
open import Data.List hiding (_∷ʳ_)

open import Relation.Binary.PropositionalEquality.TrustMe

_⇒_ : Bool → Bool → Bool
true  ⇒ true  = true
true  ⇒ false = false
false ⇒ q     = true

-- inspiration for style of proof
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



-- still required:
-- * do actual reflection


≡' : Name
≡' = quote _≡_

-- returns the number of the outermost pi quantified variables.

argsNo : Term → ℕ
argsNo (pi (arg visible relevant (el (lit _) (def Bool []))) (el s t)) = suc (argsNo t)
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
stripPi (pi (arg visible relevant (el (lit _) (def Bool []))) (el s t)) = stripPi t
-- identity otherwise
stripPi (pi args t)  = pi   args t
stripPi (var x args) = var  x    args
stripPi (con c args) = con  c    args
stripPi (def f args) = def  f    args
stripPi (lam v t)    = lam  v    t
stripPi (sort x)     = sort x
stripPi unknown      = unknown

-- examples
unsafeMinus : (a : ℕ) → (b : ℕ) → ℕ
unsafeMinus zero m = zero
unsafeMinus n₁ zero = n₁
unsafeMinus (suc n₁) (suc m) = unsafeMinus n₁ m

ff : Name
ff = quote false

tr : Name
tr = quote true

outerIsEq : (t : Term) → Bool
outerIsEq t' with stripPi t'
outerIsEq t' | (var x args) = false
outerIsEq t' | (con c args) = false
outerIsEq t' | (def f (a ∷ b ∷ c ∷ (arg _ _ (con tr [])) ∷ [])) with f ≟-Name ≡'
outerIsEq t' | (def f (a ∷ b ∷ c ∷ arg v r (con tr []) ∷ [])) | yes p = true
outerIsEq t' | (def f (a ∷ b ∷ c ∷ arg v r (con tr []) ∷ [])) | no ¬p = false
outerIsEq t' | (def f as) = false
outerIsEq t' | (lam v t) = false
outerIsEq t' | (pi t₁ t₂) = false
outerIsEq t' | (sort x) = false
outerIsEq t' | unknown = false

withoutEQ : (t : Term) → outerIsEq t ≡ true → Term
withoutEQ t pf = withoutEQ' (stripPi t) pf
  where
    withoutEQ' : Term → outerIsEq t ≡ true → Term
    withoutEQ'  (var x args) pf = {!!}
    withoutEQ'  (con c args) pf = {!!}
    withoutEQ'  (def f []) pf = {!!}
    withoutEQ'  (def f (x ∷ [])) pf = {!!}
    withoutEQ'  (def f (x ∷ x₁ ∷ [])) pf = {!!}
    withoutEQ'  (def f (x ∷ x₁ ∷ x₂ ∷ [])) pf = {!!}
    withoutEQ'  (def f (x ∷ x₁ ∷ x₂ ∷ (arg _ _ (con ff [])) ∷ [])) pf with f ≟-Name ≡'
    withoutEQ'  (def f (x ∷ x₁ ∷ arg v r x₂ ∷ arg v₁ r₁ (con ff []) ∷ [])) pf | yes p = x₂
    withoutEQ'  (def f (x ∷ x₁ ∷ x₂ ∷ arg v r (con ff []) ∷ [])) pf | no ¬p = {!!}
    withoutEQ'  (def f (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])) pf = {!!}
    withoutEQ'  (def f (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ args)) pf = {!!}
    withoutEQ'  (lam v t) pf = {!!}
    withoutEQ'  (pi t₁ t₂) pf = {!!}
    withoutEQ'  (sort x) pf = {!!}
    withoutEQ'  unknown pf = {!!}

isBoolExprQ' : (n : ℕ) → (depth : ℕ) → (t : Term) → Bool
isBoolExprQ' n depth t with stripPi t
... | t' = {!!}


isBoolExprQ : (n : ℕ) → (depth : ℕ) → (t : Term) → outerIsEq t ≡ true → Bool
isBoolExprQ n depth t pf with withoutEQ t pf
isBoolExprQ n depth t pf | t' = isBoolExprQ' n depth t'

-- the holes here should be absurds, but only Agda>=2.3.1 understands
-- the needed unification.
term2b' : (n : ℕ)
        → (depth : ℕ)
        → (t : Term)
        -- → (pf : outerIsEq t ≡ true)
        → isBoolExprQ' n 0 t ≡ true
        → BoolExpr n
term2b' n depth (var x args) pf with suc (unsafeMinus x depth) ≤? n
term2b' n depth (var x args) pf | yes p = Atomic (fromℕ≤ {unsafeMinus x depth} p)
term2b' n depth (var x args) pf | no ¬p = {!unreach!}
term2b' n depth (con tf []) pf with tf ≟-Name quote true
term2b' n depth (con tf []) pf | yes p = Truth
term2b' n depth (con tf []) pf | no ¬p with tf ≟-Name quote false
term2b' n depth (con tf []) pf | no ¬p  | yes p = Falsehood
term2b' n depth (con tf []) pf | no ¬p₁ | no ¬p = {!unreach!}
term2b' n depth (con c args) pf = {!unreach!}
term2b' n depth (def f args) pf with f ≟-Name quote _∧_
term2b' n depth (def f (arg _ _ a ∷ arg _ _ b ∷ [])) pf | yes p = And (term2b' n depth a {!!}) (term2b' n depth b {!!})
term2b' n depth (def f a) pf | yes p = {! unreach !}
term2b' n depth (def f args) pf | no ¬p with f ≟-Name quote _∨_
term2b' n depth (def f (arg _ _ a ∷ arg _ _ b ∷ [])) pf | no ¬p  | yes p = Or (term2b' n depth a {!!}) (term2b' n depth b {!!})
term2b' n depth (def f args) pf | no ¬p  | yes p = {! unreach !}
term2b' n depth (def f args) pf | no ¬p₁ | no ¬p with f ≟-Name quote _⇒_
term2b' n depth (def f (arg _ _ a ∷ arg _ _ b ∷ [])) pf | no ¬p₁ | no ¬p | yes p = Imp (term2b' n depth a {!!}) (term2b' n depth b {!!})
term2b' n depth (def f args) pf | no ¬p₁ | no ¬p | yes p = {! unreach !}
term2b' n depth (def f args) pf | no ¬p₂ | no ¬p₁ | no ¬p = {!unreach!}
term2b' n depth (lam v t) pf = {!!}
term2b' n depth (pi t₁ t₂) pf = {!!}
term2b' n depth (sort x) pf = {!!}
term2b' n depth unknown pf = {!unreach!}

-- we don't have a branch for Not, since that is immediately
-- translated as "¬ P ⇒ λ ⊥ → P"
term2b : (n : ℕ)
       → (depth : ℕ)
       → (t : Term)
       → (pf : outerIsEq t ≡ true)
       → isBoolExprQ n 0 t pf ≡ true
       → BoolExpr n
-- term2b n depth t pf with stripPi t
term2b n depth t pf pf2 = term2b' n depth (withoutEQ t pf) pf2

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
decideForallEnv {n} exp = {!!} -- hier is de truuk om op een handige manier te bewijzen dat iets een tauto is;
                                -- het is namelijk straks nodig om het in automate2 uit elkaar te pluizen...

data Diff : ℕ -> ℕ -> Set where
  Base : forall {n} -> Diff n n
  Step : forall {n m} -> Diff (suc n) m -> Diff n m

nForalls : (n m : ℕ) -> Diff n m -> BoolExpr m -> Env n -> Set
nForalls .m m Base b env = decide env b ≡ true
nForalls n m (Step y) b env = (a : Bool) -> nForalls (suc n) m y b (a ∷ env)

zeroId : (n : ℕ) -> n ≡ n + 0
zeroId zero = refl
zeroId (suc n) with n + 0 | zeroId n
zeroId (suc .w) | w | refl = refl

succLemma : (n m : ℕ) -> suc (n + m) ≡ n + suc m
succLemma zero m = refl
succLemma (suc n) m = cong suc (succLemma n m)

coerceDiff : {n m k : ℕ} -> n ≡ m -> Diff k n -> Diff k m
coerceDiff refl d = d

zero-least : (k n : ℕ) -> Diff k (k + n)
zero-least k zero = coerceDiff (zeroId k) Base
zero-least k (suc n) = Step (coerceDiff (succLemma k n) (zero-least (suc k) n))

forallBool : (m : ℕ) -> BoolExpr m -> Set
forallBool m b = nForalls zero m (zero-least 0 m) b []

foo' : {u : ⊤ × ⊤} -> ℕ
foo' = 5

foo'' : {u : ⊤ × ⊥} -> ℕ
foo'' = 5


baz : ℕ
baz = foo'

So : Bool -> Set
So true  = ⊤
So false = ⊥


forallsAcc : {n m : ℕ} -> (b : BoolExpr m) -> Env n -> Diff n m -> Set
forallsAcc b' env Base = So (decide env b')
forallsAcc b' env (Step y) = forallsAcc b' (true ∷ env) y × forallsAcc b' (false ∷ env) y

foralls : {n : ℕ} -> (b : BoolExpr n) -> Set
foralls {n} b = forallsAcc b [] (zero-least 0 n)


dif : {P : Bool -> Set} -> (b : Bool) -> P true -> P false -> P b
dif true t f = t
dif false t f = f

soundnessAcc : {m : ℕ} -> (b : BoolExpr m) ->
               {n : ℕ} -> (env : Env n) -> (d : Diff n m) ->
                forallsAcc b env d ->
               nForalls n m d b env
soundnessAcc bexp env Base H with decide env bexp
soundnessAcc bexp env Base H | true = refl
soundnessAcc bexp env Base H | false = ⊥-elim H
soundnessAcc {m} bexp {n} env (Step y) H = \a -> dif {\b -> nForalls (suc n) m y bexp (b ∷ env)} a
  (soundnessAcc bexp (true  ∷ env) y (proj₁ H))
  (soundnessAcc bexp (false ∷ env) y (proj₂ H))

soundness : {n : ℕ} -> (b : BoolExpr n) -> {i : foralls b} -> forallBool n b
soundness {n} b {i} = soundnessAcc b [] (zero-least 0 n) i

-- goalbla2 : somethm
-- goalbla2 = quoteGoal e in {!isBoolExprQ (argsNo e) 0 e refl!}

-- goaltest2 : (f f' : Bool) → f ∨ f ≡ true
-- goaltest2 = quoteGoal e in {!term2b (argsNo e) 0 e refl refl!}
-- -- modify term2b a bit.
-- goaltest3 : (f : Bool) → f ∨ f ≡ true
-- goaltest3 = quoteGoal e in {!withoutEQ e refl!}



unsafeLookup : ℕ → List Bool → Bool
unsafeLookup zero    [] = false -- pech
unsafeLookup zero    (x ∷ as) = x
unsafeLookup (suc n) [] = false -- pech
unsafeLookup (suc n) (x ∷ as) = unsafeLookup n as

interp : {n : ℕ} → BoolExpr n → List Bool → Bool
interp (Truth    ) env = true
interp (Falsehood) env = false
interp (And t t₁ ) env = interp t env ∧ interp t₁ env
interp (Or t t₁  ) env = interp t env ∨ interp t₁ env
interp (Imp t t₁ ) env = interp t env ⇒ interp t₁ env
interp (Atomic x ) env = unsafeLookup (toℕ x) env

⟦_⟧_,_ : {n : ℕ} → BoolExpr n → (m : ℕ) → List Bool → Set
⟦ t ⟧ zero    , env = interp t env ≡ true
⟦ t ⟧ (suc n) , env = (a : Bool) → ⟦ t ⟧ n , (a ∷ env)

automate2 : (t : Term)
          → (pf : outerIsEq t ≡ true)
          → (bex : isBoolExprQ (argsNo t) 0 t pf ≡ true)
          → decideForallEnv (term2b (argsNo t) 0 t pf bex) ≡ true
          → ⟦ term2b (argsNo t) 0 t pf bex ⟧ (argsNo t) , []
automate2 t pf1 pf2 pf3 = {!!}

somethm : Set
somethm = (b c : Bool) → (b ∨ true) ∧ (c ∨ c) ≡ true
-- TODO add ¬_ support

goalbla : somethm
goalbla = quoteGoal e in soundness (term2b (argsNo e) 0 e refl refl)

