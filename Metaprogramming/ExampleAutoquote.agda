module Metaprogramming.ExampleAutoquote where

open import Metaprogramming.Autoquote
open import Data.List
open import Data.Nat
open import Data.Product
open import Reflection

{-
Here we give some small examples on how one might use the Autoquote module.
Note that a much more extended real-life example is to be found in
Proofs.TautologyProver, in the last half, where boolean formulæ are quoted.
-}

-- an imaginary AST with values called S, K and I, variables with indices,
-- and a notion of joining two elements together. Suggestively named.
data Combinatory : Set where
  S K I : Combinatory
  _$_   : Combinatory → Combinatory → Combinatory
  VarC  : ℕ → Combinatory
  
-- this is what the corresponding table would look like.
skiTable : Table Combinatory
skiTable = VarC ,
           (quote  S ) # 0 ↦  S  ∷
           (quote  K ) # 0 ↦  K  ∷
           (quote  I ) # 0 ↦  I  ∷
           (quote _$_) # 2 ↦ _$_ ∷ [] 

-- the variable x here is just to introduce something
-- which is out-of-scope. Otherwise we wouldn't be able to get
-- an occurence of VarC.
trySKI0 : {a : Combinatory} → Combinatory
trySKI0 {x} = doConvert skiTable (quoteTerm ((S $ K) $ x))

-- That was easy. Let's try that again. Here's another AST,
-- this time with Peano naturals and a notion of addition. This
-- allows us to illustrate that we need not only go from S -> S as
-- in the example above (for some constructor S), but that we can also
-- model function calls such as _+_.
data Expr : Set where
  Variable : ℕ               → Expr
  Plus     : Expr → Expr     → Expr
  Succ     : Expr            → Expr
  Zero     :                   Expr

-- ...and the unsurprising table:
exprTable : Table Expr
exprTable =  Variable ,
             (quote _+_ ) # 2 ↦ Plus ∷
             (quote zero) # 0 ↦ Zero ∷
             (quote suc ) # 1 ↦ Succ ∷  []

-- you can see for yourself what happens by normalising (C-c C-n)
-- something like the expression `doConvert exprTable testterm`
testterm : {a b : ℕ} → Term
testterm {a} {b} = quoteTerm ((1 + a) + b)

testterm0 : {a : ℕ} → Term
testterm0 {a} = quoteTerm a

testterm1 : {a : ℕ} → Term
testterm1 {a} = quoteTerm 1

something : {x y : ℕ} → Expr
something {x}{y} = doConvert exprTable (quoteTerm ((2 + x + 3) + y))

-- if you felt like it, you could now build a restricted-Agda evaluator
-- in Agda, without having worried about quoting. The hairy details (which
-- can be seen in Metaprogramming.Autoquote) make this a lot finickier than
-- the way it is possible in this module.
