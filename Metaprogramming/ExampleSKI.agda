module Metaprogramming.ExampleSKI where

open import Reflection
open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality

open import Metaprogramming.ExampleUniverse
open DT
open TC
open SKI'

{-
Here we give an illustration on how to use the SKI transformer,
and that one can do this automatically using reflection. We also
give a few examples showing that in the cases we tried, the answer
also makes sense.
-}

-- say we have some lambda term which we'd like to SKI-transform:
testTerm : Term
testTerm = quoteTerm λ (n : ℕ → ℕ) → λ (m : ℕ) → n m

-- great, now testTerm holds the Agda abstract term representing the
-- given lambda abstraction.

-- using the functions exported by Metaprogramming.TypeCheck, we can
-- obtain a well-typed, well-scoped lambda term, which is the equivalent
-- of our testTerm.
testTermWT : Well-typed-closed (typeOf (term2raw testTerm)) _
testTermWT = raw2wt (term2raw testTerm)

-- we can now use the SKI-machinery and do an SKI transformation, as follows.
-- note that the type of the expression remains identical: this is the first
-- step towards argueing consistency of the procedure.
testSKI : Combinator (typeOf (term2raw testTerm))
testSKI = topCompile testTermWT

-- we can inspect the SKI term, and even though it's rather ugly, it does indeed
-- normalise to what we'd expect for our testTerm
unitTest1 : testSKI ≡ S ⟨ S ⟨ K ⟨ S ⟩ ⟩ ⟨ S ⟨ K ⟨ K ⟩ ⟩ ⟨ I ⟩ ⟩ ⟩ ⟨ K ⟨ I ⟩ ⟩
unitTest1 = refl

-- what's the use of an SKI term if we cannot use it again, as a "real" Agda term?
-- nothing indeed. Thus, we cast the ski term back to Agda as follows. As one can
-- see in the makesSense proof, we haven't lost any semantics along the way. hurrah!
toConcrete : ski2type testSKI 
toConcrete = unquote (ski2term testSKI)

{-
Note that if we'd written something like

makesSense : toConcrete ≡ (λ (n : Bool → Bool) m → n m)
...

we would get the type error that Bool != ℕ. So, even
if, when normalising the term toConcrete we get something
that looks a bit strange, everything is in fact preserved and correct.
-}

makesSense : toConcrete ≡ (λ n m → n m)
makesSense = refl

-- we can try and do the same thing for another term, that might be
-- interesting.  what would happen with this lambda term?  lets try
-- the const₄ combinator, i.e. a term which gives back the last of
-- it's 5 arguments, regardless.

const₄ : Term
const₄ = quoteTerm (λ (x y z α β : ℕ) → β)

const₄WT : Well-typed-closed (typeOf (term2raw const₄)) _
const₄WT = raw2wt (term2raw const₄)

sanity : const₄WT ≡ Lam (O Nat) (Lam (O Nat) (Lam (O Nat) (Lam (O Nat) (Lam (O Nat) (Var here)))))
sanity = refl

const₄SKI = topCompile const₄WT

letsSee : const₄SKI ≡ 
    (S ⟨ (S ⟨ K ⟨ S ⟩ ⟩) ⟨ (S ⟨ (S ⟨ K ⟨ S ⟩ ⟩) ⟨ (S ⟨ K ⟨ K ⟩ ⟩) ⟨ K ⟨ S
     ⟩ ⟩ ⟩ ⟩) ⟨ (S ⟨ (S ⟨ K ⟨ S ⟩ ⟩) ⟨ (S ⟨ K ⟨ K ⟩ ⟩) ⟨ K ⟨ K ⟩ ⟩ ⟩ ⟩) ⟨
     (S ⟨ K ⟨ K ⟩ ⟩) ⟨ K ⟨ K ⟩ ⟩ ⟩ ⟩ ⟩ ⟩) ⟨ (S ⟨ (S ⟨ K ⟨ S ⟩ ⟩) ⟨ (S ⟨ K
     ⟨ K ⟩ ⟩) ⟨ K ⟨ K ⟩ ⟩ ⟩ ⟩) ⟨ (S ⟨ K ⟨ K ⟩ ⟩) ⟨ K ⟨ I ⟩ ⟩ ⟩ ⟩
letsSee = refl

-- ok that's pretty awful, even though I'm sure it's right. unfortunately,
-- reduction isn't helping in this case.

noReduction : const₄SKI ≡ reduce₁ const₄SKI
noReduction = refl

-- oh well, back to normal Agda then?

concreteConst : ski2type const₄SKI
concreteConst = unquote (ski2term const₄SKI)

-- seems to work!
sanity₀ : concreteConst ≡ (λ _ _ _ _ z → z)
sanity₀ = refl
