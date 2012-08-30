module Metaprogramming.ExampleAutoQuote where

open import Metaprogramming.Autoquote
open import Data.List
open import Data.Nat
open import Data.Product
open import Reflection

data Combinatory : Set where
  S K I : Combinatory
  _$_   : Combinatory → Combinatory → Combinatory
  VarC  : ℕ → Combinatory
  
skiTable : Table Combinatory
skiTable = VarC ,
           0 # (quote  S ) ↦  S  ∷
           0 # (quote  K ) ↦  K  ∷
           0 # (quote  I ) ↦  I  ∷
           2 # (quote _$_) ↦ _$_ ∷ [] 

-- the variable x here is just to introduce something
-- which is out-of-scope
trySKI0 : {a : Combinatory} → Combinatory
trySKI0 {x} = doConvert skiTable (quoteTerm ((S $ K) $ x))

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

-- an illustration of getting an Expr
exprTable : Table Expr
exprTable = (Variable ,
             2 # (quote _+_ ) ↦ Plus ∷
             0 # (quote zero) ↦ Zero ∷
             1 # (quote suc ) ↦ Succ ∷
             [])

  


something : {x y : ℕ} → Expr
something {x}{y} = doConvert exprTable (quoteTerm ((2 + x + 3) + y))
