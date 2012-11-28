module Proofs.ExampleTautologies where

open import Data.Unit
open import Reflection
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Bool renaming (not to ¬_)
open import Proofs.TautologyProver
open import Proofs.Util.Handy
open import Proofs.Util.Types
open import Data.Product

-- now we can encode a tautology as follows:
-- the proof is a bit tedious though, needing a
-- case for each variable assignment.
bOrNotb : (b : Bool) → P(b ∨ ¬ b)
bOrNotb true  = tt
bOrNotb false = tt

{-
notice that u is automatically instantiated, since
there is only one option, namely tt,tt. this is special and
cool, the type system is doing work for us. Note that this is
because eta-reduction only is done in the type system for records
and not for general data types. the reason is because this is
safe in records: recursion isn't allowed.
-}
foo' : {u : ⊤ × ⊤} → ℕ
foo' = 5

baz : ℕ
baz = foo'


-- wouldn't it be nice if we could automate this?
-- eventually we'd like to prove these kinds of tautologies,
-- without needing 2ⁿ cases.
myfavouritetheorem : Set
myfavouritetheorem = (p1 q1 p2 q2 : Bool) → P(  (p1 ∨ q1) ∧ (p2 ∨ q2)
                                              ⇒ (q1 ∨ p1) ∧ (q2 ∨ p2)
                                              )

mft : myfavouritetheorem
mft = quoteGoal e in proveTautology e

anotherTheorem : (a b : Bool) → P(a ∧ b ⇒ b ∧ a)
anotherTheorem = quoteGoal e in proveTautology e

goalbla2 : (b : Bool) → P(b ∨ true)
goalbla2 = quoteGoal e in proveTautology e

not : (b : Bool) → P(b ∨ ¬ b)
not = quoteGoal e in proveTautology e

peirce : (p q  : Bool) → P(((p ⇒ q) ⇒ p) ⇒ p)
peirce = quoteGoal e in proveTautology e

foo : quoteTerm (\(x : Bool) -> x) ≡ lam visible (var 0 [])
foo = refl
