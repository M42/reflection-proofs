module Metaprogramming.Autoquote where

open import Reflection
open import Data.Unit
open import Data.Empty
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Maybe
open import Relation.Nullary.Core using (yes; no)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.Vec hiding (map)

-- here we'll try and generalise the concrete->Term->AST process
-- idea: provide a table with (Name, arity, Constructor ∈ AST) and
-- we'll try and quote it.

-- here's an example AST

data Expr : Set where
  Variable : ℕ               → Expr
  Plus     : Expr → Expr     → Expr
  Succ     : Expr            → Expr
  Zero     :                   Expr

testterm : {a b : ℕ} → Term
testterm {a} {b} = quoteTerm ((1 + a) + b)

testterm0 : {a : ℕ} → Term
testterm0 {a} = quoteTerm a

testterm1 : {a : ℕ} → Term
testterm1 {a} = quoteTerm 1

data EqN : ℕ → ℕ → Set where
  yes : {m : ℕ} → EqN m m
  no  : {m n : ℕ} → EqN m n


≟-Nat-cong : (m : ℕ) → (n : ℕ) → EqN m n → EqN (suc m) (suc n)
≟-Nat-cong .n n yes = yes
≟-Nat-cong  m n no  = no


_≟-Nat_ : (m : ℕ) → (n : ℕ) → EqN m n
zero ≟-Nat zero = yes
zero ≟-Nat suc n = no
suc m ≟-Nat zero = no
suc m ≟-Nat suc n = ≟-Nat-cong m n (m ≟-Nat n)


------
-- this is copied from the standard library, Data.Vec.N-Ary,
-- because given the variable astType we don't want to have
-- to use type-in-type.

N-ary : (n : ℕ) → Set → Set → Set
N-ary zero    A B = B
N-ary (suc n) A B = A → N-ary n A B

_$ⁿ_ : ∀ {n} {A : Set} {B : Set} → N-ary n A B → (Vec A n → B)
f $ⁿ []       = f
f $ⁿ (x ∷ xs) = f x $ⁿ xs
-- end copy from stdlib
--------

data ConstructorMapping (astType : Set) : Set₁ where
  _#_↦_ : (arity : ℕ) → Name → N-ary arity astType astType → ConstructorMapping astType




Table : Set → Set₁
Table a = ((ℕ → a) × List (ConstructorMapping a))
  
lookupName : {a : Set} → List (ConstructorMapping a) → Name → Maybe (ConstructorMapping a)
lookupName [] name = nothing
lookupName (arity # x ↦ x₁ ∷ tab) name with name ≟-Name x
lookupName (arity # x ↦ x₁ ∷ tab) name | yes p = just (arity # x ↦ x₁)
lookupName (arity # x ↦ x₁ ∷ tab) name | no ¬p = lookupName tab name

mutual
  handleNameArgs : {a : Set} → Table a → Name → List (Arg Term) → Maybe a
  handleNameArgs (vc , tab) name args with lookupName tab name
  handleNameArgs (vc , tab) name args | just (arity       # x  ↦ x₁)   with convertArgs (vc , tab) args
  handleNameArgs (vc , tab) name args | just (arity       # x₁ ↦ x₂)   | just x with length x ≟-Nat arity
  handleNameArgs (vc , tab) name args | just (.(length x) # x₁ ↦ x₂)   | just x | yes = just (x₂ $ⁿ fromList x)
  handleNameArgs (vc , tab) name args | just (arity       # x₁ ↦ x₂)   | just x | no  = nothing
  handleNameArgs (vc , tab) name args | just (arity       # x  ↦ x₁)   | nothing = nothing
  handleNameArgs (vc , tab) name args | nothing = nothing

  convertArgs : {a : Set} → Table a → List (Arg Term) → Maybe (List a)
  convertArgs tab [] = just []
  convertArgs tab (arg v r x ∷ ls) with convert tab x
  convertArgs tab (arg v r x ∷ ls) | just x₁ with convertArgs tab ls
  convertArgs tab (arg v r x ∷ ls) | just x₂ | just x₁ = just (x₂ ∷ x₁)
  convertArgs tab (arg v r x ∷ ls) | just x₁ | nothing = nothing
  convertArgs tab (arg v r x ∷ ls) | nothing = nothing
  
-- convert's arguments are:
{-
  * a : type of AST
  * variables : the constructor to use for variables. must be : ℕ → Set
  * table : a constructor table
  * the term to quote.
-}
  convert : {a : Set} → Table a → Term → Maybe a
  convert (vc , tab) (var x args) = just (vc x)
  convert (vc , tab) (con c args) = handleNameArgs (vc , tab) c args
  convert (vc , tab) (def f args) = handleNameArgs (vc , tab) f args
  convert (vc , tab) (lam v σ t)  = nothing
  convert (vc , tab) (pi t₁ t₂)   = nothing
  convert (vc , tab) (sort x)     = nothing
  convert (vc , tab) unknown      = nothing

  
convertManages : {a : Set} → Table a → Term → Set
convertManages t term with convert t term
convertManages t term | just x  = ⊤
convertManages t term | nothing = ⊥
  
exprTable : Table Expr
exprTable = (Variable ,
             2 # (quote _+_ ) ↦ Plus ∷
             0 # (quote zero) ↦ Zero ∷
             1 # (quote suc ) ↦ Succ ∷
             [])

  

doConvert : {a : Set} → (tab : Table a) → (t : Term) → {man : convertManages tab t} → a
doConvert tab t {man} with convert tab t
doConvert tab t {man} | just x = x
doConvert tab t {() } | nothing

-- an illustration of getting an Expr

something : {x y : ℕ} → Expr
something {x}{y} = doConvert exprTable (quoteTerm ((2 + x + 3) + y))
