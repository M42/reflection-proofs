module Metaprogramming.ExampleAutoQuote where

open import Metaprogramming.Autoquote
open import Data.List
open import Data.Nat
open import Data.Product

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
