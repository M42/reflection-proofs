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
testTerm : Well-typed-closed ((O Nat => O Nat) => O Nat => O Nat) 5
testTerm = Lam (O Nat => O Nat) (Lam (O Nat) (Var (there here) ⟨ Var here ⟩ ))

-- now we will perform a CPS transformation on testTerm. Since we
-- specified in Metaprogramming.ExampleUniverse that returntype should be Nat,
-- we must have a function which is of type cpsType testTerm => Nat.
-- cpsType testTerm happens to be
-- 
-- (O Nat => (O Nat => O Nat) => O Nat) => ((O Nat => (O Nat => O Nat) => O Nat) => O Nat) => O Nat    
--
-- so a continuation with type ...  should do it.

-- note that this function is the same as our original testTerm, but
-- with an extra element in the context
arg1 : WT ((
              (O Nat => (O Nat => O Nat) => O Nat)
            =>
              ((O Nat => (O Nat => O Nat) => O Nat) => O Nat)
            => O Nat
           ) ∷ []) (O Nat => (O Nat => O Nat) => O Nat) _
arg1 = Lam (O Nat) (Lam (O Nat => O Nat) (Var here ⟨ Var (there here) ⟩))

arg2 : WT ((
              (O Nat => (O Nat => O Nat) => O Nat)
            =>
              ((O Nat => (O Nat => O Nat) => O Nat) => O Nat)
            => O Nat
            ) ∷ []) ((O Nat => (O Nat => O Nat) => O Nat) => O Nat) _
arg2 = Lam (O Nat => (O Nat => O Nat) => O Nat) (Var here ⟨ Lit 4 ⟩ ⟨ Lam _ (Var here) ⟩ )

testCont : Well-typed-closed
          (
            (
              (O Nat => (O Nat => O Nat) => O Nat)
            =>
              ((O Nat => (O Nat => O Nat) => O Nat) => O Nat)
            => O Nat
            )
          => O Nat
          ) _
testCont = Lam
            (
              (O Nat => (O Nat => O Nat) => O Nat)
            =>
              ((O Nat => (O Nat => O Nat) => O Nat) => O Nat)
            => O Nat
            )
           (Var here ⟨ arg1 ⟩ ⟨ arg2 ⟩)

testCPS : Well-typed-closed RT _
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



open import Metaprogramming.Util.ExampleShow

-- try this, for example:
test = show testCPS



-- try and express factorial in WT.

true : ∀ {σ₀ σ₁ Γ} → WT Γ (σ₁ => σ₀ => σ₁) _
true {σ₀} {σ₁} = Lam σ₁ (Lam σ₀ (Var (there here)))
false : ∀ {σ₀ σ₁ Γ} → WT Γ (σ₁ => σ₀ => σ₀) _
false {σ₀} {σ₁} = Lam σ₁ (Lam σ₀ (Var here))
ifthenelse : ∀ {σ₀ σ₁ σ₂ Γ} → WT Γ ((σ₁ => σ₂ => σ₀) => σ₁ => σ₂ => σ₀) _
ifthenelse {σ₀}{σ₁}{σ₂} = Lam (σ₁ => σ₂ => σ₀) (Lam σ₁ (Lam σ₂ (Var (there (there here)) ⟨ Var (there here) ⟩ ⟨ Var here ⟩))) 

L0 : ∀ {σ} → WT [] ((σ => σ) => σ => σ) _
L0 {σ} = Lam (σ => σ) (Lam σ (Var here))

L1 : ∀ {σ} → WT [] ((σ => σ) => σ => σ) _
L1 {σ} = Lam (σ => σ) (Lam σ (Var (there here) ⟨ Var here ⟩))

L2 : ∀ {σ} → WT [] ((σ => σ) => σ => σ) _
L2 {σ} = Lam (σ => σ) (Lam σ (Var (there here) ⟨ Var (there here) ⟨ Var here ⟩ ⟩))

L3 : ∀ {σ} → WT [] ((σ => σ) => σ => σ) _
L3 {σ} = Lam (σ => σ) (Lam σ (Var (there here) ⟨ Var (there here) ⟨ Var (there here) ⟨ Var here ⟩ ⟩ ⟩))

succ : ∀ {σ} → WT [] (((σ => σ => σ) => σ) => (σ => σ => σ) => σ => σ) _
succ {σ} = Lam ((σ => σ => σ) => σ) (Lam (σ => σ => σ) (Lam  σ ( Var (there here) ⟨ Var (there (there here)) ⟨ Var (there here) ⟩ ⟩ ⟨ Var here ⟩  )))

zero? : ∀ {σ} → WT [] (((σ => σ => σ) => (σ => σ => σ) => (σ => σ => σ) => σ) => σ) _
zero? {σ} = Lam ((σ => σ => σ) =>
                   (σ => σ => σ) =>
                   (σ => σ => σ) => σ) ( ( ( Var here ⟨ true ⟩ ) ⟨ false ⟩ ) ⟨ true ⟩ )

Lplus : ∀ {t t1 t2 t3} → WT [] ((t3 => t1 => t2 => t) => (t3 => t1) => t3 => t2 => t) _
Lplus {t}{t1}{t2}{t3} = Lam (t3 => t1 => t2 => t)
                            (Lam (t3 => t1)
                                 (Lam t3
                                      (Lam t2 ( Var (there (there (there here))) ⟨ Var (there here) ⟩ ⟨ Var (there (there here)) ⟨ Var (there here) ⟩ ⟩ ⟨ Var here ⟩ ))))

Ltimes : ∀ {t t1 t2} → WT [] ((t1 => t2 => t) => t1 => t2 => t) _
Ltimes {t}{t1}{t2} = Lam (t1 => t2 => t) (Lam t1 (Lam t2 ( Var (there (there here)) ⟨ Var (there here) ⟩ ⟨ Var here ⟩ )))

Lpredecessor : WT [] {!!} _
Lpredecessor = {!!}


fix : ∀ {a Γ} → WT Γ ((a => a) => a) _
fix {a} = Lam (a => a) (Var here ⟨ fix ⟨ (Var here) ⟩ ⟩ )

{-

fix :: (a -> a) -> a
fix f = f (fix f)
Y = Ly.(Lx.(y)(x)x)Lx.(y)(x)x



pred = \ n -> (((n) (\ p -> (\ z -> ((z)(succ)(p)true)(p)true))) (\ z -> ((z)0)0)) false
-}
