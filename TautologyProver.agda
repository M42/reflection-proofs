module TautologyProver where

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

infixr 4 _⇒_
_⇒_ : Bool → Bool → Bool
true  ⇒ true  = true
true  ⇒ false = false
false ⇒ true  = true
false ⇒ false = true

data Error (a : String) : Set where

So : String → Bool → Set
So _ true  = ⊤
So s false = Error s

P : Bool → Set
P = So "Expression isn't shizzle?"

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
myfavouritetheorem = (p1 q1 p2 q2 : Bool) → P(  (p1 ∨ q1) ∧ (p2 ∨ q2)
                                              ⇒ (q1 ∨ p1) ∧ (q2 ∨ p2)
                                              )

-- we'll make some DSL into which we're going to translate theorems
-- (which are actually types of functions), and then use reflection
-- in some unmagical way... see below.

{-
The point of having SET is to have a place to put stuff subst gives us.
i.e., if we want to go from BoolExpr → Set, we need a way to reattach a
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
decide env (Imp p q)    = decide env p ⇒ decide env q
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


outerIsSo : (t : Term) → Bool
outerIsSo (var x args) = false
outerIsSo (con c args) = false
outerIsSo (def f args) with Data.Nat._≟_ (length args) 2
outerIsSo (def f args) | yes p with tt
outerIsSo (def f [])                        | yes () | tt
outerIsSo (def f (x ∷ []))                  | yes () | tt
outerIsSo (def f (a ∷ arg v r x ∷ []))      | yes p  | tt with f ≟-Name quote So
outerIsSo (def f (a ∷ arg v r x ∷ [])) | yes p₁ | tt | yes p = true
outerIsSo (def f (a ∷ arg v r x ∷ [])) | yes p | tt | no ¬p = false
outerIsSo (def f (x ∷ x₃ ∷ x₄ ∷ args))      | yes () | tt
outerIsSo (def f args)                      | no ¬p with tt
outerIsSo (def f [])                        | no ¬p | tt = false
outerIsSo (def f (x ∷ xs))                  | no ¬p | tt = false
outerIsSo (lam v t)                         = false
outerIsSo (pi t₁ t₂)                        = false
outerIsSo (sort x)                          = false
outerIsSo unknown                           = false


withoutSo : (t : Term) → outerIsSo t ≡ true → Term
withoutSo (var x args) ()
withoutSo (con c args) ()
withoutSo (def f args) pf with Data.Nat._≟_ (length args) 2
withoutSo (def f args) pf | yes p with tt
withoutSo (def f [])   pf                      | yes () | tt
withoutSo (def f (x ∷ [])) pf                  | yes () | tt
withoutSo (def f (a ∷ arg v r x ∷ [])) pf      | yes p  | tt with f ≟-Name quote So
withoutSo (def f (a ∷ arg v r x ∷ [])) pf  | yes p₁ | tt | yes p = x
withoutSo (def f (a ∷ arg v r x ∷ [])) () | yes p | tt | no ¬p
withoutSo (def f (x ∷ x₃ ∷ x₄ ∷ args)) pf     | yes () | tt
withoutSo (def f args)             pf         | no ¬p with tt
withoutSo (def f []) () | no ¬p | tt
withoutSo (def f (x ∷ xs)) () | no ¬p | tt
withoutSo (lam v t)    ()
withoutSo (pi t₁ t₂)   ()
withoutSo (sort x)     ()
withoutSo unknown      ()


isBoolExprQ' : (n : ℕ) → (t : Term) → Bool
isBoolExprQ' n (var x args) with suc (unsafeMinus x 0) ≤? n
isBoolExprQ' n (var x args) | yes p = true
isBoolExprQ' n (var x args) | no ¬p = false
isBoolExprQ' n (con tf as) with Data.Nat._≟_ 0 (length as)
isBoolExprQ' n (con tf []) | yes pp with tf ≟-Name quote true
isBoolExprQ' n (con tf []) | yes pp | yes p = true
isBoolExprQ' n (con tf []) | yes pp | no ¬p with tf ≟-Name quote false
isBoolExprQ' n (con tf []) | yes pp | no ¬p  | yes p = true
isBoolExprQ' n (con tf []) | yes pp | no ¬p₁ | no ¬p = false
isBoolExprQ' n (con tf (x ∷ as)) | yes p = false
isBoolExprQ' n (con tf []) | no ¬p = false
isBoolExprQ' n (con tf (a ∷ s)) | no ¬p = false
isBoolExprQ' n (def f []) = false
isBoolExprQ' n (def f (arg v r x ∷ [])) with f ≟-Name quote ¬_
isBoolExprQ' n (def f (arg v r x ∷ [])) | yes p = isBoolExprQ' n x
isBoolExprQ' n (def f (arg v r x ∷ [])) | no ¬p = false
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) with f ≟-Name quote _∧_
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | yes p = (isBoolExprQ' n x) ∧ (isBoolExprQ' n x₁)
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | no ¬p with f ≟-Name quote _∨_
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | no ¬p | yes p = (isBoolExprQ' n x) ∧ (isBoolExprQ' n x₁)
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | no ¬p₁ | no ¬p with f ≟-Name quote _⇒_
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | no ¬p₁ | no ¬p | yes p = (isBoolExprQ' n x) ∧ (isBoolExprQ' n x₁)
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | no ¬p₂ | no ¬p₁ | no ¬p = false
isBoolExprQ' n (def f (x ∷ x₁ ∷ x₂ ∷ args)) = false
isBoolExprQ' n (lam v t) = false
isBoolExprQ' n (pi t₁ t₂) = false
isBoolExprQ' n (sort y) = false
isBoolExprQ' n unknown = false

isBoolExprQSo : (freeVars : ℕ) → (t : Term) → outerIsSo t ≡ true → Bool
isBoolExprQSo n t pf with withoutSo t pf
isBoolExprQSo n t pf | t' = isBoolExprQ' n t'

-- the holes here should be absurds, but only Agda>=2.3.1 manages
-- the unification.
term2b' : (n : ℕ)
        → (t : Term)
        → isBoolExprQ' n t ≡ true
        → BoolExpr n
term2b' n (var x args) pf with suc (unsafeMinus x 0) ≤? n
term2b' n (var x args) pf | yes p = Atomic (fromℕ≤ {unsafeMinus x 0} p)
term2b' n (var x args) () | no ¬p
term2b' n (con tf []) pf with tf ≟-Name quote true
term2b' n (con tf []) pf | yes p = Truth
term2b' n (con tf []) pf | no ¬p with tf ≟-Name quote false
term2b' n (con tf []) pf | no ¬p  | yes p = Falsehood
term2b' n (con tf []) () | no ¬p₁ | no ¬p
term2b' n (con c (a ∷ rgs)) ()
term2b' n (def f []) ()
term2b' n (def f (arg v r x ∷ [])) pf with f ≟-Name quote ¬_
term2b' n (def f (arg v r x ∷ [])) pf | yes p = Not (term2b' n x pf)
term2b' n (def f (arg v r x ∷ [])) () | no ¬p
term2b' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) pf with f ≟-Name quote _∧_
term2b' n (def f (arg a₁ b₁ x ∷ arg a b x₁ ∷ [])) pf | yes p = And
  (term2b' n x (and-l pf))
  (term2b' n x₁ (and-r (isBoolExprQ' n x) (isBoolExprQ' n x₁) pf))
term2b' n (def f (arg a₁ b₁ x ∷ arg a b x₁ ∷ [])) pf | no p with f ≟-Name quote _∨_
term2b' n (def f (arg a₁ b₁ x ∷ arg a b x₁ ∷ [])) pf | no ¬p | yes p = Or
  (term2b' n x (and-l pf))
  (term2b' n x₁ (and-r (isBoolExprQ' n x) (isBoolExprQ' n x₁) pf))
term2b' n (def f (arg a₁ b₁ x ∷ arg a b x₁ ∷ [])) pf | no ¬p | no p with f ≟-Name quote _⇒_
term2b' n (def f (arg a₁ b₁ x ∷ arg a b x₁ ∷ [])) pf | no ¬p₁ | no ¬p | yes p = Imp
  (term2b' n x (and-l pf))
  (term2b' n x₁ (and-r (isBoolExprQ' n x) (isBoolExprQ' n x₁) pf))
term2b' n (def f (arg a₁ b₁ x ∷ arg a b x₁ ∷ [])) () | no ¬p | no p | no p₁
term2b' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ x₂ ∷ args)) ()
term2b' n (lam v t)  ()
term2b' n (pi t₁ t₂) ()
term2b' n (sort x)   ()
term2b' n unknown    ()

term2bSo : (n : ℕ)
       → (t : Term)
       → (pf : outerIsSo t ≡ true)
       → isBoolExprQSo n t pf ≡ true
       → BoolExpr n
term2bSo n t pf pf2 = term2b' n (withoutSo t pf) pf2

-- useful for things like Env n → Env m → Env n ⊕ m
_⊕_ : ℕ → ℕ → ℕ
zero  ⊕ m = m
suc n ⊕ m = n ⊕ suc m

data Diff : ℕ → ℕ → Set where
  Base : ∀ {n}   → Diff n n
  Step : ∀ {n m} → Diff (suc n) m → Diff n m


buildPiSo : (n m : ℕ) → Diff n m → BoolExpr m → Env n → Set
buildPiSo .m m (Base  ) b env = P(decide env b)
buildPiSo n m  (Step y) b env = (a : Bool) → buildPiSo (suc n) m y b (a ∷ env)

zeroId : (n : ℕ) → n ≡ n + 0
zeroId zero                           = refl
zeroId (suc  n) with n + 0 | zeroId n
zeroId (suc .w)    | w     | refl     = refl

succLemma : (n m : ℕ) → suc (n + m) ≡ n + suc m
succLemma zero m    = refl
succLemma (suc n) m = cong suc (succLemma n m)

coerceDiff : {n m k : ℕ} → n ≡ m → Diff k n → Diff k m
coerceDiff refl d = d

zero-least : (k n : ℕ) → Diff k (k + n)
zero-least k zero    = coerceDiff (zeroId k) Base
zero-least k (suc n) = Step (coerceDiff (succLemma k n) (zero-least (suc k) n))

forallBoolSo : (m : ℕ) → BoolExpr m → Set
forallBoolSo m b = buildPiSo zero m (zero-least 0 m) b []
{-
notice that u is automatically instantiated, since
there is only one option, namely tt,tt. this is special and
cool, the type system is doing work for us. Note that this is
because eta-reduction only is done in the type system for records
and not for general data types. possibly the reason is because this is
safe in records because recursion isn't allowed. question for agda-café?
-}
foo' : {u : ⊤ × ⊤} → ℕ
foo' = 5

foo'' : {u : ⊤ × ⊥} → ℕ
foo'' = 5

baz : ℕ
baz = foo'

-- very much like ⊥-elim, but for errors.
Error-elim : ∀ {Whatever : Set} {e : String} → Error e → Whatever
Error-elim ()


forallsAcc : {n m : ℕ} → (b : BoolExpr m) → Env n → Diff n m → Set
forallsAcc b' env (Base  ) = So "Expression isn't a tautology" (decide env b')
forallsAcc b' env (Step y) = forallsAcc b' (true ∷ env) y × forallsAcc b' (false ∷ env) y

foralls : {n : ℕ} → (b : BoolExpr n) → Set
foralls {n} b = forallsAcc b [] (zero-least 0 n)

-- dependently typed If
dif : {P : Bool → Set} → (b : Bool) → P true → P false → P b
dif true  t f = t
dif false t f = f

soundnessAccSo : {m : ℕ} → (b : BoolExpr m) →
               {n : ℕ} → (env : Env n) → (d : Diff n m) →
               forallsAcc b env d →
               buildPiSo n m d b env
soundnessAccSo     bexp     env Base     H with decide env bexp
soundnessAccSo     bexp     env Base     H | true  = H
soundnessAccSo     bexp     env Base     H | false = Error-elim H
soundnessAccSo {m} bexp {n} env (Step y) H =
  λ a → dif {λ b → buildPiSo (suc n) m y bexp (b ∷ env)} a
    (soundnessAccSo bexp (true  ∷ env) y (proj₁ H))
    (soundnessAccSo bexp (false ∷ env) y (proj₂ H))

soundnessSo : {n : ℕ} → (b : BoolExpr n) → {i : foralls b} → forallBoolSo n b
soundnessSo {n} b {i} = soundnessAccSo b [] (zero-least 0 n) i

goalbla2 : (b : Bool) → P(b ∨ true)
goalbla2 = quoteGoal e in soundnessSo (term2bSo (argsNo e) (stripPi e) refl refl)

not : (b : Bool) → P(b ∨ ¬ b)
not = quoteGoal e in soundnessSo (term2bSo (argsNo e) (stripPi e) refl refl)

peirce : (p q  : Bool) → P(((p ⇒ q) ⇒ p) ⇒ p)
peirce = quoteGoal e in soundnessSo (term2bSo (argsNo e) (stripPi e) refl refl)

mft : myfavouritetheorem
mft = quoteGoal e in soundnessSo (term2bSo (argsNo e) (stripPi e) refl refl)

anotherTheorem : (a b : Bool) → P(a ∧ b ⇒ b ∧ a)
anotherTheorem = quoteGoal e in soundnessSo (term2bSo (argsNo e) (stripPi e) refl refl)
