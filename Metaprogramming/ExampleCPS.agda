module Metaprogramming.ExampleCPS where

open import Data.List
open import Data.Nat

map/k : {a b : Set} → (a → (a → b) → b) → List a → (List a → b) → b
map/k f/k []       k = k []
map/k f/k (x ∷ xs) k = f/k x (λ v → (map/k f/k xs (λ v-rest → k (v ∷ v-rest))))

testlist : List ℕ
testlist = 1 ∷ 2 ∷ 3 ∷ []

identity : {a : Set} → a → a
identity x = x

incrlist  : List ℕ
incrlist  = map/k (λ n k → k (suc n)) testlist identity
-- ... as opposed to
incrlist' : List ℕ
incrlist' = map (λ n → suc n) testlist

open import Metaprogramming.ExampleUniverse
open CPS'


-- how does CPS work?? give an illustration!
