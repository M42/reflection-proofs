open import Equal
open import Reflection
open import Data.Maybe

module TypeCheck (U : Set) (equal? : (x : U) → (y : U) → Equal? x y) (type? : Name → Maybe U) (Uel : U → Set) (quoteVal : (x : U) → Term → Uel x) (quoteBack : (x : U) → Uel x → Term) where

open import Data.Stream using (Stream ; evens ; odds ; _∷_ )
open import Coinduction
open import Data.Maybe
open import Data.Empty
open import Data.Product hiding (map)
open import Data.Unit hiding (_≤_; _≤?_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Core
open import Data.String renaming (_++_ to _+S+_)
open import Data.Fin hiding (_+_ ; _<_; _≤_) renaming (compare to fcompare)
open import Data.List
open import Data.Nat renaming (_≟_ to _≟-Nat_)
open import Data.Bool hiding (T) renaming (_≟_ to _≟Bool_)

import Datatypes
open module DT = Datatypes U equal? Uel

----------------------------------------------------------------
-- examples.
wellScoped : Term -- :: (O => O) => (O => O)
wellScoped = quoteTerm (λ (x : Set → Set) → λ (y : Set) → x y)

sth : Term -- :: ℕ
sth = quoteTerm (λ (y : ℕ → ℕ) → y 5)
----------------------------------------------------------------


-- type checking:
-- here we expect as input the type of the whole expression. It's a checker, not
-- an inferrer. This is inspired by the lambdapi paper by löh, mcbride, swierstra


open import Relation.Nullary.Core

-- we won't care about sorts here.
type2ty'  : Type → Maybe U'
type2ty' (el s (var x args)) = nothing
type2ty' (el s (con c args)) with type? c
type2ty' (el s (con c args)) | just x = just (O x)
type2ty' (el s (con c args)) | nothing = nothing
type2ty' (el s (def f args)) with type? f
type2ty' (el s (def f args)) | just x = just (O x)
type2ty' (el s (def f args)) | nothing = nothing
type2ty' (el s (lam v ty t)) = nothing -- type2ty ty => O {!!} -- err, we don't support types with lambdas (pi types)
--type2ty' (el s (pi (arg v r x) t₂)) = {!!} -- (type2ty x => type2ty t₂
type2ty' (el s (pi (arg v r x) t₂)) with type2ty' x | type2ty' t₂
type2ty' (el s (pi (arg v r x) t₂)) | just x₁ | just x₂ = just (x₁ => x₂)
type2ty' (el s (pi (arg v r x) t₂)) | just x₁ | nothing = nothing
type2ty' (el s (pi (arg v r x) t₂)) | nothing | b = nothing
type2ty' (el s (sort x)) = nothing
type2ty' (el s unknown) = nothing
-- if you get an incomplete
-- pattern matching here... this happens when a lambda wasn't
-- annotated. the Type is then `unknown', even though that's not a
-- constructor of type Type

type2ty'just : Type → Set
type2ty'just t with type2ty' t
... | nothing = ⊥
... | just x  = ⊤

type2ty : (t : Type) → type2ty'just t → U'
type2ty t pf with type2ty' t
type2ty t pf | just x = x
type2ty t () | nothing

mutual
  isVarReasonable : ℕ → List (Arg Term) → Set
  isVarReasonable x  l         with length l ≟-Nat 0
  isVarReasonable x  []                | yes p = ⊤
  isVarReasonable x₁ (x ∷ l)           | yes ()
  isVarReasonable x  l                 | no ¬p with length l ≟-Nat 1
  isVarReasonable x  []                | no ¬p  | yes ()
  isVarReasonable x₁ (arg a b c ∷ [])  | no ¬p  | yes p = isLambdaQ' c
  isVarReasonable x₂ (x ∷ x₁ ∷ l)      | no ¬p  | yes ()
  isVarReasonable x ls | no ¬p₁ | no ¬p with length ls ≤? 2
  isVarReasonable x [] | no ¬p₁ | no ¬p | yes p = ⊥
  isVarReasonable x₁ (arg v r x ∷ []) | no ¬p₁ | no ¬p | yes p = ⊥
  isVarReasonable x₂ (x ∷ x₁ ∷ []) | no ¬p₁ | no ¬p | yes p = ⊥
  isVarReasonable x₃ (x ∷ x₁ ∷ x₂ ∷ ls) | no ¬p₁ | no ¬p | yes (s≤s (s≤s ()))
  isVarReasonable x [] | no ¬p₂ | no ¬p₁ | no ¬p = ⊥
  isVarReasonable x₁ (arg v r x ∷ ls) | no ¬p₂ | no ¬p₁ | no ¬p = ⊥

  isLambdaQ' : (t : Term) → Set
  isLambdaQ' (lam v sigma t) = type2ty'just sigma × isLambdaQ' t
  isLambdaQ' (var a b)       = isVarReasonable a b
  isLambdaQ' (def f args)    = ⊥
  isLambdaQ' (con c args)    with type? c
  isLambdaQ' (con c args) | just x = ⊤
  isLambdaQ' (con c args) | nothing = ⊥
  isLambdaQ' (pi t₁ t₂)      = ⊥
  isLambdaQ' (sort x)        = ⊥
  isLambdaQ' unknown         = ⊥



term2raw :  (t : Term) →
            {pf : isLambdaQ' t} →
            Raw
term2raw (lam v sigma t)           {(pf₀ , pf)} = Lam (type2ty sigma pf₀) (term2raw t {pf})
term2raw (var x  l)                {pf}  with length l ≟-Nat 0
term2raw (var x  [])               {pf}        | yes p = Var x
term2raw (var x₁ (x ∷ l))          {pf}        | yes ()
term2raw (var x  l)                {pf}        | no ¬p with length l ≟-Nat 1
term2raw (var x  [])               {pf}        | no ¬p  | yes ()
term2raw (var x₁ (arg a b c ∷ [])) {pf} | no ¬p  | yes p = App (Var x₁) (term2raw c {pf})
term2raw (var x₂ (x ∷ x₁ ∷ l))     {pf} | no ¬p  | yes ()
term2raw (var x ls)                {pf} | no ¬p₁ | no ¬p with length ls ≤? 2
term2raw (var x [])                {()} | no ¬p₁ | no ¬p | yes p
term2raw (var x₁ (arg v r x ∷ [])) {pf} | no ¬p₁ | no ¬p | yes p = ⊥-elim (¬p refl)
term2raw (var x₂ (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) {()} | no ¬p₁ | no ¬p | yes p
term2raw (var x₃ (x ∷ x₁ ∷ x₂ ∷ ls)) {pf} | no ¬p₁ | no ¬p | yes (s≤s (s≤s ()))
term2raw (var x [])                 {()} | no ¬p₂ | no ¬p₁ | no ¬p
term2raw (var x₁ (arg v r x ∷ []))  {pf} | no ¬p₂ | no ¬p₁ | no ¬p = ⊥-elim (¬p₁ refl)
term2raw (var x₂ (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) {()} | no ¬p₂ | no ¬p₁ | no ¬p
term2raw (var x₃ (arg v r x ∷ arg v₁ r₁ x₁ ∷ x₂ ∷ ls)) {()} | no ¬p₂ | no ¬p₁ | no ¬p
term2raw (def f args)      {()}
term2raw (con c args)      {pf} with type? c
term2raw (con c args)      {pf} | just x = Lit x (quoteVal x (con c args))
term2raw (con c args)      {()} | nothing
term2raw (pi t₁ t₂)        {()}
term2raw (sort x)          {()}
term2raw unknown           {()}


-- this is from Ulf's tutorial.
infer : (Γ : Ctx)(e : Raw) → Infer Γ e
infer Γ (Lit ty x) = ok 1 (O ty) (Lit {_}{ty} x)
infer Γ (Var x) with Γ ! x
infer Γ (Var .(index p))      | inside σ p = ok 1 σ (Var p)
infer Γ (Var .(length Γ + m)) | outside m = bad
infer Γ (App e e₁) with infer Γ e
infer Γ (App .(erase t) e₁) | ok n (Cont a) t = bad
infer Γ (App .(erase t) e₁) | ok n (O x) t = bad
infer Γ (App .(erase t) e₁) | ok n (τ => τ₁) t with infer Γ e₁
infer Γ (App .(erase t₁) .(erase t₂)) | ok n (σ => τ) t₁   | ok n₂ σ' t₂ with σ =?= σ'
infer Γ (App .(erase t₁) .(erase t₂)) | ok n (.σ' => τ) t₁ | ok n₂ σ' t₂ | yes = ok _ τ (t₁ ⟨ t₂ ⟩ )
infer Γ (App .(erase t₁) .(erase t₂)) | ok n (σ => τ) t₁   | ok n₂ σ' t₂ | no = bad
infer Γ (App .(erase t) e₁) | ok n (τ => τ₁) t | bad = bad
infer Γ (App e e₁) | bad = bad
infer Γ (Lam σ e) with infer (σ ∷ Γ) e
infer Γ (Lam σ .(erase t)) | ok n τ t = ok _ (σ => τ) (Lam σ t)
infer Γ (Lam σ e) | bad = bad



typechecks : Raw → Set
typechecks r with infer [] r
typechecks .(erase t) | ok n τ t   = ⊤
typechecks r          | bad      = ⊥


-- given a Raw lambda plus a proof (⊤) that it typechecks;
-- give the type of the expression.
typeOf : (r : Raw) → {pf : typechecks r} → U'
typeOf r {pf} with infer [] r
typeOf .(erase t) | ok n τ t = τ
typeOf r {()}     | bad

sizeOf : (r : Raw) → {pf : typechecks r} → ℕ
sizeOf r {pf} with infer [] r
sizeOf .(Datatypes.erase U equal? Uel t) | Datatypes.ok n τ t = n
sizeOf r {()} | Datatypes.bad

raw2wt : {n : ℕ} (r : Raw) → {pf : typechecks r} → WT [] (typeOf r {pf}) (sizeOf r {pf})
raw2wt {n} r {pf} with infer [] r
raw2wt {n} .(erase t) | ok n₁ τ t = t
raw2wt {n} r {()}     | bad

open import Apply

lam2type : {σ : U'} {Γ : Ctx} {n : ℕ} → WT Γ σ n → Set
lam2type {σ} t = el' σ

lam2term : {σ : U'} {Γ : Ctx} {n : ℕ} → WT Γ σ n → Term
lam2term (Lit {_}{σ} x)   = quoteBack σ x
lam2term (Var x)          = var (index x) []
-- somehow type inference doesn't work here, i.e. we cannot introduce
-- 2 lam's and apply t₁ to t₂ that way.
lam2term (t₁ ⟨ t₂ ⟩)      = def (quote Apply) (arg visible relevant (lam2term t₁) ∷
                                               arg visible relevant (lam2term t₂) ∷ [])
lam2term (Lam σ t)        = lam visible (el unknown unknown) (lam2term t)

