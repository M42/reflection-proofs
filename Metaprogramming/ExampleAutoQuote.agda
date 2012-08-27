module ExampleAutoQuote where

import AutoQuote
open import Data.List

open import TypeCheck

skiTable : Table Combinatory
skiTable = Entry 0 (quote  S )  S  ∷
           Entry 0 (quote  K )  K  ∷
           Entry 0 (quote  I )  I  ∷
           Entry 2 (quote _$_) _$_ ∷ [] 

trySKI0 : {a : Combinatory} → Combinatory
trySKI0 {x} = doConvert VarC skiTable (quoteTerm ((S $ K) $ x))
