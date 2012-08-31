module Metaprogramming.ExampleCPS where

open import Data.List
open import Data.Nat

-- assume the normal map function, which *returns* the modified
-- list. here is a CPS-transformed version of map, which applies
-- some function f/k to all elements, then calls the continuation
-- on that new list.
map/k : {a b : Set} → (a → (a → b) → b) → List a → (List a → b) → b
map/k f/k []       k = k []
map/k f/k (x ∷ xs) k = f/k x (λ v → (map/k f/k xs (λ v-rest → k (v ∷ v-rest))))

-- a test list and function which is usable as a continuation. id
-- functions are often used as "final return" statents in CPS, to be able
-- to get hold of the answer even though returning is considered evil.
testlist : List ℕ
testlist = 1 ∷ 2 ∷ 3 ∷ []
identity : {a : Set} → a → a
identity x = x

-- compare the way we invoke the CPS-map compared to usual:
incrlist  : List ℕ
incrlist  = map/k (λ n k → k (suc n)) testlist identity
-- ... as opposed to
incrlist' : List ℕ
incrlist' = map (λ n → suc n) testlist
-- note also that the modification function (λ n k → k (suc n)) in this case,
-- or (+1) in simpler notation, also is CPS-style and takes a continuation.

open import Relation.Binary.PropositionalEquality

we'renotlying : incrlist ≡ incrlist'
we'renotlying = refl

open import Metaprogramming.ExampleUniverse
open DT
open CPS'

-- now, on to an illustration of the usage and effect of the CPS transformation
-- developed in Metaprogramming.CPS

-- this term is equivalent to λ x → λ (y : ℕ) → x y
testTerm : WT [] ((O Nat => O Nat) => O Nat => O Nat) 5
testTerm = Lam (O Nat => O Nat) (Lam (O Nat) (Var (there here) ⟨ Var here ⟩ ))

-- now we will perform a CPS transformation on testTerm. Since we
-- specified in Metaprogramming.ExampleUniverse that returntype should be Nat,
-- we must have a function which is of type cpsType testTerm => Nat.
-- cpsType testTerm happens to be
-- 
-- (O Nat => (O Nat => O Nat) => O Nat) => ((O Nat => (O Nat => O Nat) => O Nat) => O Nat) => O Nat    
--
-- so a continuation with type ...  should do it.

testCont : WT [] (((O Nat
                      =>
                      (O Nat
                       =>
                       O Nat)
                      =>
                      O Nat)
                     =>
                     ((O Nat
                       =>
                       (O Nat
                        =>
                        O Nat)
                       =>
                       O Nat)
                      =>
                      O Nat)
                     =>
                     O Nat)
                    =>
                    O Nat) _
testCont = Lam ((O Nat => (O Nat => O Nat) => O Nat) =>
                  ((O Nat => (O Nat => O Nat) => O Nat) => O Nat) => O Nat) (Lit zero)

testCPS : WT [] RT _
testCPS = T testTerm testCont

testCPSis : testCPS ≡ testCont 
                        ⟨ Lam (O Nat => (O Nat => O Nat) => O Nat)
                              (Lam ((O Nat => (O Nat => O Nat) => O Nat) => O Nat)
                                   (Var here ⟨ Lam (O Nat)
                                                 (Lam (O Nat => O Nat)
                                                     (Lam (O Nat => (O Nat => O Nat) => O Nat)
                                                         (Lam (O Nat)
                                                           (Var (there here) ⟨ Var here ⟩ ⟨ Var (there (there here)) ⟩)
                                                           ⟨ Var (there (there here)) ⟩) ⟨ Var (there (there (there here))) ⟩)) ⟩)) ⟩
testCPSis = refl

{-
Note that something like the above is way less painful to the eyes when
using the provided show function, defined for WT.

i.e. C-c C-n show testCPS
-}

{-

One might wonder why this seemingly universally-useful showing code
isn't in, say, a Util module or in the Datatypes module. The reason for
this is that the Datatypes module, where WT resides, is parameterised, since
in the Lit constructor it may contain an arbitrary user-chosen type. This
introduces difficulties when defining show, since the BUILTIN INTEGER pragma
may not be used in a parameterised module. If one then works around that and puts
the builtin-integer bit elsewhere, the results still aren't satisfactory, since
the output is the cluttered with fully-qualified function names, such as Metaprogramming.Util.Show.primStringAppend ...
-}


{- a bit of code to make WT-terms a lot easier to look at. -}
open import Data.String renaming (_++_ to _+S+_)
postulate
  Int    : Set
{-# BUILTIN INTEGER Int    #-}

primitive
    -- Integer functions
  primNatToInteger    : ℕ → Int
  primShowInteger     : Int → String

showℕ : ℕ → String
showℕ = λ x → primShowInteger (primNatToInteger x)

show : ∀ {Γ σ n} → WT Γ σ n → String
show (Var x)      = "$" +S+ showℕ (index x)
show (wt ⟨ wt₁ ⟩) = show wt +S+ " ⟨ " +S+ show wt₁ +S+ "⟩"
show (Lam σ wt)   = "(λ. " +S+ show wt +S+ ")"
show (Lit x₁)     = "literal" -- we don't print literal values, since we have no idea what type they have right now.

{- end printing code -}

-- try this, for example:
test = show testCPS
