module SKITest where

open import ExampleUniverse
open import Reflection
open import Data.Nat
open import Relation.Binary.PropositionalEquality

open DT
open TC

open import Data.List
import SKI
open module SK = SKI U equal? type? Uel quoteVal quoteBack

st1 = quoteTerm \ (x : ℕ → ℕ) → \ (y : ℕ) → x y

someterm1 : WT [] (typeOf (term2raw st1))
someterm1 = raw2wt (term2raw st1)

someterm : NamedWT [] (typeOf (term2raw st1))
someterm = unbrown (raw2wt (term2raw st1))

someSKI : Comb [] (typeOf (term2raw st1))
someSKI = topCompile someterm


id1 = quoteTerm λ (n : ℕ) → n

term1 : NamedWT [] (typeOf (term2raw id1))
term1 = unbrown( raw2wt (term2raw id1))

testTerm : Term
testTerm = quoteTerm λ (n : ℕ → ℕ) → λ (m : ℕ) → n m

testQ : WT [] (typeOf (term2raw testTerm))
testQ = raw2wt (term2raw testTerm)

testSKI : Comb [] (typeOf (term2raw testTerm))
testSKI = topCompile (unbrown testQ)

unitTest1 : testSKI ≡ (S ⟨ (S ⟨ K ⟨ S ⟩ ⟩) ⟨ (S ⟨ K ⟨ K ⟩ ⟩) ⟨ I ⟩ ⟩ ⟩) ⟨ K ⟨ I ⟩ ⟩
unitTest1 = refl

toConcrete : ski2type testSKI 
toConcrete = unquote (ski2term testSKI)
