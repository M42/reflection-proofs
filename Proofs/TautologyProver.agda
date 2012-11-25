module Proofs.TautologyProver where

open import Relation.Binary.PropositionalEquality renaming ([_] to by ; subst to substpe)
open import Data.String
open import Data.Nat
open import Relation.Nullary hiding (¬_)
open import Reflection
open import Data.Bool renaming (not to ¬_ )
open import Data.Fin hiding (_+_; pred)
open import Data.Vec renaming (reverse to vreverse ; map to vmap; foldr to vfoldr; _++_ to _v++_)
open import Data.Unit hiding (_≤?_)
open import Data.Empty
open import Data.Product hiding (map)
open import Data.List hiding (_∷ʳ_)
open import Proofs.Util.Handy
open import Proofs.Util.Types
open import Proofs.Util.Lemmas

-- we'll make some DSL into which we're going to translate theorems,
-- and using reflection, we'll translate concrete Agda into our
-- boolean-expression-DSL
data BoolExpr : ℕ → Set where
  Truth     : {n : ℕ}                           → BoolExpr n
  Falsehood : {n : ℕ}                           → BoolExpr n
  And       : {n : ℕ} → BoolExpr n → BoolExpr n → BoolExpr n
  Or        : {n : ℕ} → BoolExpr n → BoolExpr n → BoolExpr n
  Not       : {n : ℕ} → BoolExpr n              → BoolExpr n
  Imp       : {n : ℕ} → BoolExpr n → BoolExpr n → BoolExpr n
  Atomic    : {n : ℕ} → Fin n                   → BoolExpr n

-- the environment, defined as follows, along with the interpretation
-- function ⟦_⊢_⟧, can reconstruct the concrete value of an abstract
-- boolean expression. Note that the length of the environment
-- corresponds to the number of free variables in the boolean expression.
Env : ℕ → Set
Env = Vec Bool

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

-- counts the number of the outermost pi quantified variables.  this
-- will be used to determine how many free variables (n) to allow in
-- the abstract boolean expression representation BoolExpr n.
freeVars : Term → ℕ
freeVars (pi (arg visible relevant (el (lit _) (def Bool []))) (el s t)) = suc (freeVars t)
freeVars (pi a b)     = 0
freeVars (var x args) = 0
freeVars (con c args) = 0
freeVars (def f args) = 0
freeVars (lam v t)  = 0
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
stripPi (lam v t)  = lam  v   t
stripPi (sort x)     = sort x
stripPi unknown      = unknown

-- a check-function, or predicate, to determine if the thing which has
-- been quoted is a Term wrapped in a call to So(), which P()
-- normalises to.
isSoExprQ : (t : Term) → Set
isSoExprQ (var x args) = ⊥
isSoExprQ (con c args) = ⊥
isSoExprQ (def f args) with Data.Nat._≟_ (length args) 2
isSoExprQ (def f args) | yes p with tt
isSoExprQ (def f [])                   | yes () | tt
isSoExprQ (def f (x ∷ []))             | yes () | tt
isSoExprQ (def f (a ∷ arg v r x ∷ [])) | yes p  | tt with f ≟-Name quote So
isSoExprQ (def f (a ∷ arg v r x ∷ [])) | yes p₁ | tt | yes p = ⊤
isSoExprQ (def f (a ∷ arg v r x ∷ [])) | yes p  | tt | no ¬p = ⊥
isSoExprQ (def f (x ∷ x₃ ∷ x₄ ∷ args)) | yes () | tt
isSoExprQ (def f args)                 | no ¬p with tt
isSoExprQ (def f [])                   | no ¬p | tt = ⊥
isSoExprQ (def f (x ∷ xs))             | no ¬p | tt = ⊥
isSoExprQ (lam v t)                  = ⊥
isSoExprQ (pi t₁ t₂)                   = ⊥
isSoExprQ (sort x)                     = ⊥
isSoExprQ unknown                      = ⊥

-- assuming the predicate isSoExprQ above, return the
-- argument to So, which should be the boolean expression
-- we want.
stripSo : (t : Term) → isSoExprQ t → Term
stripSo (var x args)                 ()
stripSo (con c args)                 ()
stripSo (def f args)                 pf with Data.Nat._≟_ (length args) 2
stripSo (def f args) pf | yes p with tt -- doing "with tt" at the end
                                        -- is necessary in some cases,
                                        -- to force normalisation of preceding
                                        -- arguments.
stripSo (def f [])                   pf | yes () | tt
stripSo (def f (x ∷ []))             pf | yes () | tt
stripSo (def f (a ∷ arg v r x ∷ [])) pf | yes p  | tt with f ≟-Name quote So
stripSo (def f (a ∷ arg v r x ∷ [])) pf | yes p₁ | tt | yes p = x
stripSo (def f (a ∷ arg v r x ∷ [])) () | yes p  | tt | no ¬p
stripSo (def f (x ∷ x₃ ∷ x₄ ∷ args)) pf | yes () | tt
stripSo (def f args)                 pf | no ¬p with tt
stripSo (def f [])                   () | no ¬p | tt
stripSo (def f (x ∷ xs))             () | no ¬p | tt
stripSo (lam v t)                  ()
stripSo (pi t₁ t₂)                   ()
stripSo (sort x)                     ()
stripSo unknown                      ()

-- this function generates the "original" goal type, by introducing
-- m boolean variables, which are added to the environment, and finally
-- calling the interpretation function on the expression under that environment.
-- this gives back something like the ∀ a b c → P (a ∧ b ...) we would have
-- started with.
-- The Diff argument is a promise that in the end, m and n will be equal.
-- see the corresponding section in the documentation for a more complete explanation.
proofGoal' : (n m : ℕ) → Diff n m → BoolExpr m → Env n → Set
proofGoal' .m m (Base  ) b env = P ⟦ env ⊢ b ⟧ 
proofGoal' n m  (Step y) b env = (a : Bool) → proofGoal' (suc n) m y b (a ∷ env)

-- ...and this is the 'outer' function to generate the full proof obligation / goal / type.
proofGoal : (m : ℕ) → BoolExpr m → Set
proofGoal m b = proofGoal' zero m (zero-least 0 m) b []

-- this is the decision function, like even? in the IsEven module. It is
-- only inhabitable (returns ⊤) if all branches, i.e. possible variable assignments,
-- result in a true (and because of P()) a ⊤ value.
-- we will eventually exploit that this results in a pair of pairs of unit values,
-- which are inferrable, being record types.
forallsAcc : {n m : ℕ} → (b : BoolExpr m) → Env n → Diff n m → Set
forallsAcc b' env (Base  ) = P ⟦ env ⊢ b' ⟧
forallsAcc b' env (Step y) = forallsAcc b' (true ∷ env) y × forallsAcc b' (false ∷ env) y

foralls : {n : ℕ} → (b : BoolExpr n) → Set
foralls {n} b = forallsAcc b [] (zero-least 0 n)

-- in this function, we prove that if we are able to inhabit the type
-- generated by foralls, we can also inhabit the original goal type,
-- which we recover using proofGoal. since we know the structure of the
-- predicate foralls, we can anticipate and pick the correct branch, depending
-- on the assignment of the variables in the environment, and show that any other
-- path through this pair-of-pairs is absurd.
soundnessAcc : {m : ℕ} →
                 (b : BoolExpr m) →
                 {n : ℕ} →
                 (env : Env n) →
                 (d : Diff n m) →
                 forallsAcc b env d →
                 proofGoal' n m d b env
soundnessAcc     bexp     env Base     H with ⟦ env ⊢ bexp ⟧
soundnessAcc     bexp     env Base     H | true  = H
soundnessAcc     bexp     env Base     H | false = Error-elim H
soundnessAcc {m} bexp {n} env (Step y) H =
  λ a → if {λ b → proofGoal' (suc n) m y bexp (b ∷ env)} a
    (soundnessAcc bexp (true  ∷ env) y (proj₁ H))
    (soundnessAcc bexp (false ∷ env) y (proj₂ H))

soundness : {n : ℕ} → (b : BoolExpr n) → {i : foralls b} → proofGoal n b
soundness {n} b {i} = soundnessAcc b [] (zero-least 0 n) i

{-
Now we have most of the ingredients we need to be able to automatically
generate tautology-proofs for arbitrary boolean exrpessions. The only missing
part in the chain

   concrete expression -> abstract expression -> proof generation -> cast back to concrete goal and proof

is the first arrow, the concrete to abstract translation. This is where the
reflection API is going to help us; using quoteGoal we'll inspect the
proof obligation and generate an abstract representation of the boolean expression
that the user is trying to get a proof for.

We have developed the module Autoquote which will hide a lot of ugly technicalities
regarding quoting, but one thing it doesn't support is constraints such as the Fin n
we have in our BoolExpr datatype. Thus, we will first quote to a similar datatype, but
which allows any Natural in the variable spot. Afterwards we can ensure that the
expression returned is sensible, and make all the |ℕ|s into |Fin n|s.
-}
open import Metaprogramming.Autoquote

-- here is a simplified version of BoolExpr. The only difference is the
-- Atomic constructor, which holds naturals instead of Fin n's.
data BoolInter : Set where
  Truth     :                                       BoolInter
  Falsehood :                                       BoolInter
  And       : BoolInter → BoolInter → BoolInter
  Or        : BoolInter → BoolInter → BoolInter
  Not       : BoolInter                    → BoolInter
  Imp       : BoolInter → BoolInter → BoolInter
  Atomic    : ℕ                                   → BoolInter
  
-- this is the translation table we need: refer to the thesis or the
-- Metaprogramming.ExampleAutoquote module for more details on how
-- and why this works.
boolTable : Table BoolInter
boolTable = (Atomic ,
              2 # (quote _∧_  ) ↦ And
            ∷ 2 # (quote _∨_  ) ↦ Or
            ∷ 1 # (quote  ¬_  ) ↦ Not
            ∷ 0 # (quote true ) ↦ Truth
            ∷ 0 # (quote false) ↦ Falsehood
            ∷ 2 # (quote _⇒_  ) ↦ Imp         ∷ [])

-- we can now convert a Term (Agda's abstract syntax) into our BoolInter
-- datatype relatively painlessly.
term2boolexpr' : (t : Term) → {pf : convertManages boolTable t} → BoolInter
term2boolexpr' t {pf} = doConvert boolTable t {pf}

-- this predicate reflects the notion of a Term having at most n
-- free variables. Each variable reference (Atomic's argument) must
-- be smaller than this maximum n to be able to fit into BoolExpr
bool2finCheck : (n : ℕ) → (t : BoolInter) → Set
bool2finCheck n Truth        = ⊤
bool2finCheck n Falsehood    = ⊤
bool2finCheck n (And t t₁)   = bool2finCheck n t × bool2finCheck n t₁
bool2finCheck n (Or t t₁)    = bool2finCheck n t × bool2finCheck n t₁
bool2finCheck n (Not t)      = bool2finCheck n t
bool2finCheck n (Imp t t₁)   = bool2finCheck n t × bool2finCheck n t₁
bool2finCheck n (Atomic x)   with suc x ≤? n
bool2finCheck n (Atomic x)   | yes p = ⊤
bool2finCheck n (Atomic x)   | no ¬p = ⊥

-- assuming all's well with the variables, we can cast:
bool2fin : (n : ℕ) → (t : BoolInter) → (bool2finCheck n t) → BoolExpr n
bool2fin n Truth       pf = Truth
bool2fin n Falsehood   pf = Falsehood
bool2fin n (And t t₁) (p₁ , p₂) = And (bool2fin n t p₁) (bool2fin n t₁ p₂)
bool2fin n (Or t t₁)  (p₁ , p₂) = Or (bool2fin n t p₁) (bool2fin n t₁ p₂)
bool2fin n (Not t)     p₁ = Not (bool2fin n t p₁)
bool2fin n (Imp t t₁) (p₁ , p₂) =  Imp (bool2fin n t p₁) (bool2fin n t₁ p₂)
bool2fin n (Atomic x)  p₁ with suc x ≤? n
bool2fin n (Atomic x)  p₁ | yes p = Atomic (fromℕ≤ {x} p)
bool2fin n (Atomic x)  () | no ¬p

-- and now we have a function which goes directly from the output of quoteGoal
-- (i.e. a Term which should be a boolean expression wrapped in P() and preceded by
-- zero or more ∀ (b : Bool) →'s) to a BoolExpr. We've had to make the type rather ugly
-- since we need a number of predicates on the shape and properties of the term.
concrete2abstract :
         (t : Term)
       → let noPi = stripPi t
             n    = freeVars t in
         {pf : isSoExprQ noPi}
       → let t' = stripSo noPi pf in
            {pf2 : convertManages boolTable t'}
          → (bool2finCheck n (term2boolexpr' t' {pf2}))
          → BoolExpr n
concrete2abstract t {pf} {pf2} fin = bool2fin (freeVars t) (term2boolexpr' (stripSo (stripPi t) pf) {pf2}) fin

-- proveTautology is the final API we expose to the user: it accepts a number
-- of implicit arguments so that the user needn't worry about anything except passing
-- the term to be proven. The result of using this technique is that if an invalid
-- argument is passed (such as a malformed boolean expression or something which isn't
-- a tautology) we get unsolved metas for the hidden arguments, which might look like
-- compilation hasn't failed, while in fact, these unsolved metas constitute proofs
-- we cannot give (of type ⊥, for example).
proveTautology : (t : Term) →
     let noPi = stripPi t
         n    = freeVars t in
        {pf : isSoExprQ noPi} →
           let t' = stripSo noPi pf in
                {pf2 : convertManages boolTable t'} → 
                {fin : bool2finCheck n (term2boolexpr' t' {pf2})} → 
                let b = concrete2abstract t {pf} {pf2} fin in
                    {i : foralls b} →
                    proofGoal n b
proveTautology e {pf} {pf2} {fin} {i} = soundness {freeVars e} (concrete2abstract e fin) {i}

