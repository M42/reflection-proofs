module Metaprogramming.ExampleUniverse where

open import Reflection
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.Product
open import Data.Maybe
open import Data.Nat hiding (_<_ ; _>_) renaming (_≟_ to _≟-Nat_) 
open import Metaprogramming.Util.Equal
open import Relation.Nullary.Core
open import Induction.WellFounded

{-
this module illustrates how to parameterise the SKI, CPS etc. modules
with your own universe. For the purposes of instruction we'll keep it simple,
but you are free to use more complicated universes. There is no support
for parameterised universes, however; a universe is just a type index.
-}

-- ok, here's an example universe. We have something called Nat, which
-- we decide should stand for the natural numbers. Arrow types needn't be
-- modeled; the universes U' internal to the Datatypes etc modules already handle
-- this.
data U : Set where
  Nat : U

-- we need to provide a function which gives back the name of any constructor in our universe.
-- since this requires pattern matching, the library cannot do this without our help. (in the strict
-- sense, such as here where we only have one constructor, we don't, in fact, need pattern matching,
-- but since something like `quote x` where x is the parameter in τ = (O x), in some WT [] τ n, returns
-- "var 0 []" instead of the value of x quoted (see thesis for complete discussion), this is necessary.)
?type : U → Name
?type Nat = quote ℕ

-- this function is the interpretation -- translate our abstract
-- types into their corresponding Agda types.
Uel : U → Set
Uel Nat = ℕ

-- since we support literal values, in theory we're the only ones
-- who know how to turn them back into "real" Agda. we will provide
-- a helper function to the library
quoteBack : (x : U) → Uel x → Term
quoteBack Nat zero    = con (quote zero) []
quoteBack Nat (suc x) = con (quote suc) (arg visible relevant (quoteBack Nat x) ∷ [])

-- we also need to implement decidable equality for our universe,
-- since this does rely on pattern matching.
equal? : (x : U) → (y : U) → Equal? x y
equal? Nat Nat = yes

-- this is the type we'd like for our CPS transformation's continuation function return value.
-- we choose just a natural (not that we have much choice with a one-element universe).
halttype : U
halttype = Nat

-- we also want a function which, given a name of a concrete value,
-- returns its type in our universe. we may fail, of course -- the
-- function wouldn't be total otherwise.
type? : Name → Maybe U
type? n with n ≟-Name (quote suc)
type? n | yes p = just Nat
type? n | no ¬p with n ≟-Name (quote zero)
type? n | no ¬p | yes p = just Nat
type? n | no ¬p₁ | no ¬p with n ≟-Name (quote ℕ)
type? n | no ¬p₁ | no ¬p | yes p = just Nat
type? n | no ¬p₂ | no ¬p₁ | no ¬p = nothing

-- this function turns an abstract Agda term into a value
-- which our universe should represent. in our case, we recognise
-- and return natural values.
quoteVal : (x : U) → Term → Uel x
quoteVal Nat (var x args) = 0
quoteVal Nat (con c args) with c ≟-Name quote zero
quoteVal Nat (con c args) | yes p = 0
quoteVal Nat (con c args) | no ¬p with c ≟-Name quote suc
quoteVal Nat (con c []) | no ¬p | yes p = 0
quoteVal Nat (con c (arg v r x ∷ args)) | no ¬p | yes p = 1 + quoteVal Nat x
quoteVal Nat (con c args) | no ¬p₁ | no ¬p = 0
quoteVal Nat      _       = 0

-- now that we have these required helper modules, we can instantiate all
-- the library modules using them as parameters.
------------------------

-- now define aliases for the modules
import Metaprogramming.Datatypes
open module DT = Metaprogramming.Datatypes U equal? Uel
import Metaprogramming.TypeCheck
open module TC = Metaprogramming.TypeCheck U equal? type? Uel quoteVal quoteBack
import Metaprogramming.CPS
open module CPS' = Metaprogramming.CPS U Uel equal? type? quoteBack halttype
import Metaprogramming.SKI
open module SKI' = Metaprogramming.SKI U equal? type? Uel quoteVal quoteBack

{-
for actual examples of the use of the different modules, refer to
the Examples* modules. Here we only instantiate the modules for later
use.
-}

g : Raw
g = term2raw (quoteTerm (λ (n : ℕ) → n))
a : Raw
a = term2raw (quoteTerm 7)

test0 : Raw
test0 = App g a

typedtest0 : WT [] (typeOf test0) (sizeOf test0)
typedtest0 = raw2wt test0

viewTypedTest0 : typedtest0 ≡ Lam (O Nat) (Var here) ⟨ Lit 7 ⟩
viewTypedTest0 = refl
