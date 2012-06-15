module TautologyProver where

open import Relation.Binary.PropositionalEquality renaming ([_] to by ; subst to substpe)
open import Data.String
open import Data.Maybe hiding (Eq)
open import Data.Nat
open import Relation.Nullary hiding (¬_)
open import Data.Product hiding (map)
open import Data.Vec.Properties
open import Data.Nat.Properties
open import Relation.Binary hiding (_⇒_)
open import Reflection

open import Data.Vec.N-ary
open import Data.Bool renaming (not to ¬_ )
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
P = So "Expression doesn't evaluate to true in this branch."

bOrNotb : (b : Bool) → b ∨ ¬ b ≡ true
bOrNotb true  = refl
bOrNotb false = refl

bImpb : (b : Bool) → P(b ⇒ b)
bImpb true  = tt
bImpb false = tt

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
⟦_⊢_⟧ : ∀ {n : ℕ} (e : Env n) → BoolExpr n → Bool
⟦ env ⊢ Truth      ⟧ = true
⟦ env ⊢ Falsehood  ⟧ = false
⟦ env ⊢ And be be₁ ⟧ = ⟦ env ⊢ be ⟧ ∧ ⟦ env ⊢ be₁ ⟧
⟦ env ⊢ Or be be₁  ⟧ = ⟦ env ⊢ be ⟧ ∨ ⟦ env ⊢ be₁ ⟧
⟦ env ⊢ Not be     ⟧ = ¬ ⟦ env ⊢ be ⟧
⟦ env ⊢ Imp be be₁ ⟧ = ⟦ env ⊢ be ⟧ ⇒ ⟦ env ⊢ be₁ ⟧
⟦ env ⊢ Atomic n   ⟧ = lookup n env

-- returns the number of the outermost pi quantified variables.

freeVars : Term → ℕ
freeVars (pi (arg visible relevant (el (lit _) (def Bool []))) (el s t)) = suc (freeVars t)
freeVars (pi a b)     = 0
freeVars (var x args) = 0
freeVars (con c args) = 0
freeVars (def f args) = 0
freeVars (lam v t)    = 0
freeVars (sort x)     = 0
freeVars unknown      = 0

-- peels off all the outermost Pi constructors,
-- returning a term with freeVars free variables.

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


isSoExprQ : (t : Term) → Set
isSoExprQ (var x args) = ⊥
isSoExprQ (con c args) = ⊥
isSoExprQ (def f args) with Data.Nat._≟_ (length args) 2
isSoExprQ (def f args) | yes p with tt
isSoExprQ (def f [])                        | yes () | tt
isSoExprQ (def f (x ∷ []))                  | yes () | tt
isSoExprQ (def f (a ∷ arg v r x ∷ []))      | yes p  | tt with f ≟-Name quote So
isSoExprQ (def f (a ∷ arg v r x ∷ [])) | yes p₁ | tt | yes p = ⊤
isSoExprQ (def f (a ∷ arg v r x ∷ [])) | yes p | tt | no ¬p = ⊥
isSoExprQ (def f (x ∷ x₃ ∷ x₄ ∷ args))      | yes () | tt
isSoExprQ (def f args)                      | no ¬p with tt
isSoExprQ (def f [])                        | no ¬p | tt = ⊥
isSoExprQ (def f (x ∷ xs))                  | no ¬p | tt = ⊥
isSoExprQ (lam v t)                         = ⊥
isSoExprQ (pi t₁ t₂)                        = ⊥
isSoExprQ (sort x)                          = ⊥
isSoExprQ unknown                           = ⊥


stripSo : (t : Term) → isSoExprQ t → Term
stripSo (var x args) ()
stripSo (con c args) ()
stripSo (def f args) pf with Data.Nat._≟_ (length args) 2
stripSo (def f args) pf | yes p with tt
stripSo (def f [])   pf                      | yes () | tt
stripSo (def f (x ∷ [])) pf                  | yes () | tt
stripSo (def f (a ∷ arg v r x ∷ [])) pf      | yes p  | tt with f ≟-Name quote So
stripSo (def f (a ∷ arg v r x ∷ [])) pf  | yes p₁ | tt | yes p = x
stripSo (def f (a ∷ arg v r x ∷ [])) () | yes p | tt | no ¬p
stripSo (def f (x ∷ x₃ ∷ x₄ ∷ args)) pf     | yes () | tt
stripSo (def f args)             pf         | no ¬p with tt
stripSo (def f []) () | no ¬p | tt
stripSo (def f (x ∷ xs)) () | no ¬p | tt
stripSo (lam v t)    ()
stripSo (pi t₁ t₂)   ()
stripSo (sort x)     ()
stripSo unknown      ()


isBoolExprQ' : (n : ℕ) → (t : Term) → Set
isBoolExprQ' n (var x args) with suc (unsafeMinus x 0) ≤? n
isBoolExprQ' n (var x args) | yes p = ⊤
isBoolExprQ' n (var x args) | no ¬p = ⊥
isBoolExprQ' n (con tf as) with Data.Nat._≟_ 0 (length as)
isBoolExprQ' n (con tf []) | yes pp with tf ≟-Name quote true
isBoolExprQ' n (con tf []) | yes pp | yes p = ⊤
isBoolExprQ' n (con tf []) | yes pp | no ¬p with tf ≟-Name quote false
isBoolExprQ' n (con tf []) | yes pp | no ¬p  | yes p = ⊤
isBoolExprQ' n (con tf []) | yes pp | no ¬p₁ | no ¬p = ⊥
isBoolExprQ' n (con tf (x ∷ as)) | yes ()
isBoolExprQ' n (con tf []) | no ¬p = ⊥-elim (¬p refl)
isBoolExprQ' n (con tf (a ∷ s)) | no ¬p = ⊥
isBoolExprQ' n (def f []) = ⊥
isBoolExprQ' n (def f (arg v r x ∷ [])) with f ≟-Name quote ¬_
isBoolExprQ' n (def f (arg v r x ∷ [])) | yes p = isBoolExprQ' n x
isBoolExprQ' n (def f (arg v r x ∷ [])) | no ¬p = ⊥
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) with f ≟-Name quote _∧_
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | yes p = (isBoolExprQ' n x) × (isBoolExprQ' n x₁)
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | no ¬p with f ≟-Name quote _∨_
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | no ¬p | yes p = (isBoolExprQ' n x) × (isBoolExprQ' n x₁)
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | no ¬p₁ | no ¬p with f ≟-Name quote _⇒_
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | no ¬p₁ | no ¬p | yes p = (isBoolExprQ' n x) × (isBoolExprQ' n x₁)
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | no ¬p₂ | no ¬p₁ | no ¬p = ⊥
isBoolExprQ' n (def f (x ∷ x₁ ∷ x₂ ∷ args)) = ⊥
isBoolExprQ' n (lam v t) = ⊥
isBoolExprQ' n (pi t₁ t₂) = ⊥
isBoolExprQ' n (sort y) = ⊥
isBoolExprQ' n unknown = ⊥

isBoolExprQ : (freeVars : ℕ) → (t : Term) → isSoExprQ t → Set
isBoolExprQ n t pf with stripSo t pf
isBoolExprQ n t pf | t' = isBoolExprQ' n t'

term2boolexpr : (n : ℕ)
        → (t : Term)
        → isBoolExprQ' n t
        → BoolExpr n
term2boolexpr n (var x args) pf with suc (unsafeMinus x 0) ≤? n
term2boolexpr n (var x args) pf | yes p = Atomic (fromℕ≤ {unsafeMinus x 0} p)
term2boolexpr n (var x args) () | no ¬p
term2boolexpr n (con tf []) pf with tf ≟-Name quote true
term2boolexpr n (con tf []) pf | yes p = Truth
term2boolexpr n (con tf []) pf | no ¬p with tf ≟-Name quote false
term2boolexpr n (con tf []) pf | no ¬p  | yes p = Falsehood
term2boolexpr n (con tf []) () | no ¬p₁ | no ¬p
term2boolexpr n (con c (a ∷ rgs)) ()
term2boolexpr n (def f []) ()
term2boolexpr n (def f (arg v r x ∷ [])) pf with f ≟-Name quote ¬_
term2boolexpr n (def f (arg v r x ∷ [])) pf | yes p = Not (term2boolexpr n x pf)
term2boolexpr n (def f (arg v r x ∷ [])) () | no ¬p
term2boolexpr n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) pf with f ≟-Name quote _∧_
term2boolexpr n (def f (arg a₁ b₁ x ∷ arg a b x₁ ∷ [])) (proj₁ , proj₂) | yes p = And
  (term2boolexpr n x proj₁)
  (term2boolexpr n x₁ proj₂)
term2boolexpr n (def f (arg a₁ b₁ x ∷ arg a b x₁ ∷ [])) pf | no p with f ≟-Name quote _∨_
term2boolexpr n (def f (arg a₁ b₁ x ∷ arg a b x₁ ∷ [])) (proj₁ , proj₂) | no ¬p | yes p = Or
  (term2boolexpr n x proj₁)
  (term2boolexpr n x₁ proj₂)
term2boolexpr n (def f (arg a₁ b₁ x ∷ arg a b x₁ ∷ [])) pf | no ¬p | no p with f ≟-Name quote _⇒_
term2boolexpr n (def f (arg a₁ b₁ x ∷ arg a b x₁ ∷ [])) (proj₁ , proj₂) | no ¬p₁ | no ¬p | yes p = Imp
  (term2boolexpr n x proj₁)
  (term2boolexpr n x₁ proj₂)
term2boolexpr n (def f (arg a₁ b₁ x ∷ arg a b x₁ ∷ [])) () | no ¬p | no p | no p₁
term2boolexpr n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ x₂ ∷ args)) ()
term2boolexpr n (lam v t)  ()
term2boolexpr n (pi t₁ t₂) ()
term2boolexpr n (sort x)   ()
term2boolexpr n unknown    ()

-- useful for things like Env n → Env m → Env n ⊕ m
_⊕_ : ℕ → ℕ → ℕ
zero  ⊕ m = m
suc n ⊕ m = n ⊕ suc m

data Diff : ℕ → ℕ → Set where
  Base : ∀ {n}   → Diff n n
  Step : ∀ {n m} → Diff (suc n) m → Diff n m


prependTelescope : (n m : ℕ) → Diff n m → BoolExpr m → Env n → Set
prependTelescope .m m (Base  ) b env = P ⟦ env ⊢ b ⟧ 
prependTelescope n m  (Step y) b env = (a : Bool) → prependTelescope (suc n) m y b (a ∷ env)

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
forallBoolSo m b = prependTelescope zero m (zero-least 0 m) b []

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

baz : ℕ
baz = foo'

-- very much like ⊥-elim, but for Errors.
Error-elim : ∀ {Whatever : Set} {e : String} → Error e → Whatever
Error-elim ()

forallsAcc : {n m : ℕ} → (b : BoolExpr m) → Env n → Diff n m → Set
forallsAcc b' env (Base  ) = P ⟦ env ⊢ b' ⟧
forallsAcc b' env (Step y) = forallsAcc b' (true ∷ env) y × forallsAcc b' (false ∷ env) y

foralls : {n : ℕ} → (b : BoolExpr n) → Set
foralls {n} b = forallsAcc b [] (zero-least 0 n)

-- dependently typed if-statement
if : (P : Bool → Set) → (b : Bool) → P true → P false → P b
if p true  t f = t
if p false t f = f

soundnessAcc : {m : ℕ} →
                 (b : BoolExpr m) →
                 {n : ℕ} →
                 (env : Env n) →
                 (d : Diff n m) →
                 forallsAcc b env d →
                 prependTelescope n m d b env
soundnessAcc     bexp     env Base     H with ⟦ env ⊢ bexp ⟧
soundnessAcc     bexp     env Base     H | true  = H
soundnessAcc     bexp     env Base     H | false = Error-elim H
soundnessAcc {m} bexp {n} env (Step y) H =
  λ a → if (λ b → prependTelescope (suc n) m y bexp (b ∷ env)) a
    (soundnessAcc bexp (true  ∷ env) y (proj₁ H))
    (soundnessAcc bexp (false ∷ env) y (proj₂ H))

soundness : {n : ℕ} → (b : BoolExpr n) → {i : foralls b} → forallBoolSo n b
soundness {n} b {i} = soundnessAcc b [] (zero-least 0 n) i

concrete2abstract :   (t : Term)
       → {pf : isSoExprQ (stripPi t)}
       → {pf2 : isBoolExprQ (freeVars t) (stripPi t) pf}
       → BoolExpr (freeVars t)
concrete2abstract t {pf} {pf2} = term2boolexpr (freeVars t) (stripSo (stripPi t) pf) pf2

proveTautology : (t : Term) →
        {pf : isSoExprQ (stripPi t)} →
        {pf2 : isBoolExprQ (freeVars t) (stripPi t) pf} →
        let b = concrete2abstract t {pf} {pf2} in
        {i : foralls b} →
        forallBoolSo (freeVars t) b
proveTautology e {pf} {pf2} {i} = soundness {freeVars e} (concrete2abstract e) {i}

anotherTheorem : (a b : Bool) → P(a ∧ b ⇒ b ∧ a)
anotherTheorem = quoteGoal e in proveTautology e

goalbla2 : (b : Bool) → P(b ∨ true)
goalbla2 = quoteGoal e in proveTautology e

not : (b : Bool) → P(b ∨ ¬ b)
not = quoteGoal e in proveTautology e

peirce : (p q  : Bool) → P(((p ⇒ q) ⇒ p) ⇒ p)
peirce = quoteGoal e in proveTautology e

mft : myfavouritetheorem
mft = quoteGoal e in proveTautology e


-- acknowledge Ruud:
-- thing : {err : String} {a : Bool} → So err a → a ≡ true
-- thing ⊤ = {!!}
-- 
-- another : (a b : Bool) → a ∧ b ⇒ b ∧ a ≡ true
-- another a b with anotherTheorem a b
-- ...  | asdf = {!asdf!}
