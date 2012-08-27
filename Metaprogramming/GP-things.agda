module GP-things where


open import Reflection
open import Data.Fin
open import Data.List
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Core
open import Data.Unit using (⊤ ; tt)
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Function

data Col : Set where
  R G B : Col
  -- Bleen : ℕ → Col


isDT : Definition → Set
isDT (data-type x) = ⊤
isDT _             = ⊥

dt : (d : Definition) → isDT d → Data-type
dt (data-type x) pf = x
dt (function x)  ()
dt (record′ x)   ()
dt constructor′  ()
dt axiom         ()
dt primitive′    ()

-- this tells us if a (constructor's) type is "simple"
isUnit : Type → Set
isUnit (el s (var x args)) = ⊥
isUnit (el s (con c args)) = ⊥
isUnit (el s (def f [])) = ⊤
isUnit (el s (def f (x ∷ args))) = ⊥
isUnit (el s (lam v ty t)) = ⊥
isUnit (el s (pi t₁ t₂)) = ⊥
isUnit (el s (sort x)) = ⊥
isUnit (el s unknown) = ⊥


allConsUnit : List Name → Set
allConsUnit [] = ⊤
allConsUnit (x ∷ xs) =  isUnit (type x) × allConsUnit xs

  
isomorphicDT : (n : Name) → {isdt : isDT (definition n)} → Set
isomorphicDT n {isdt} with (constructors (dt (definition n) isdt)) 
... | cs with allConsUnit cs | length cs
isomorphicDT n | cs | s | r = {!!}

-- We capture that two sets are isomorphic using the following record.
record Iso (A B : Set) : Set where
  field
    from    : A → B
    to      : B → A
    from-to : {x : B} → from (to x) ≡ x
    to-from : {x : A} → to (from x) ≡ x


isIn : (acc : ℕ) → (total : ℕ) → Name → List Name → Set
isIn acc tot n [] = ⊥
isIn acc tot n (x ∷ xs) with n ≟-Name x
isIn acc tot n (x ∷ xs) | yes p with suc acc ≤? tot
isIn acc tot n (x ∷ xs) | yes p₁ | yes p = ⊤
isIn acc tot n (x ∷ xs) | yes p | no ¬p = ⊥
isIn acc tot n (x ∷ xs) | no ¬p = isIn (suc acc) tot n xs

indexIn : (acc : ℕ) → (total : ℕ) → (n : Name) → (ns : List Name) → isIn acc total n ns → Fin total
indexIn acc total n [] ()
indexIn acc total n (x ∷ ns) pf with n ≟-Name x
indexIn acc total n (x ∷ ns)  y  | yes p with suc acc ≤? total
indexIn acc total n (x ∷ ns) y | yes p₁ | yes p = fromℕ≤ {acc} p
indexIn acc total n (x ∷ ns) () | yes p | no ¬p
indexIn acc total n (x ∷ ns)  y  | no  p = indexIn (suc acc) total n ns y
    
isName : Term → Set
isName (var x args) = ⊥
isName (con c args) = ⊤
isName (def f args) = ⊤
isName (lam v ty t) = ⊥
isName (pi t₁ t₂) = ⊥ -- maaaaybe still useful since type.
isName (sort x) = ⊥
isName unknown = ⊥

-- this is needed since doing (c : Col) → quote c
-- gives us var 0 [] in the best case :(
cons2name : (c : Col) → Name
cons2name R = quote R
cons2name G = quote G
cons2name B = quote B

-- this is something we need to do because the unquote keyword cannot
-- handle terms, just constructors. kind-of logical since the process isn't
-- lazy and should splice code at compile-time as if the user had written
-- it.
unquote' : Term → Col
unquote' (var x args) = {!!}
unquote' (con c args) = {!!}
unquote' (def f args) with f ≟-Name (quote R)
unquote' (def f args) | yes p = R
unquote' (def f args) | no ¬p with f ≟-Name (quote G)
unquote' (def f args) | no ¬p | yes p = G
unquote' (def f args) | no ¬p₁ | no ¬p with f ≟-Name (quote B)
unquote' (def f args) | no ¬p₁ | no ¬p | yes p = B
unquote' (def f args) | no ¬p₂ | no ¬p₁ | no ¬p = {!!}
unquote' (lam v ty t) = {!!}
unquote' (pi t₁ t₂) = {!!}
unquote' (sort x) = {!!}
unquote' unknown = {!!}


mappingFrom : (c : Col)
                → {pf2 : isIn 0 (length (constructors (dt (definition (quote Col)) tt))) (cons2name c) (  constructors (dt (definition (quote Col)) tt)) }
                → Fin 3
mappingFrom c {pf2} = indexIn 0 (length (constructors (dt (definition (quote Col)) tt))) (cons2name c) ((constructors (dt (definition (quote Col)) tt))) pf2

_!_ : {n : ℕ} {A : Set} → Vec A n → Fin n → A
(x ∷ vs) ! zero = x
[] ! ()
(x ∷ vs) ! suc f = vs ! f

mappingTo : Fin 3 → Col
mappingTo f with fromList (constructors (dt (definition (quote Col)) tt))
... | a     with Data.Vec.map (λ name → (def name [])) a
... | b     with b ! f
... | c = unquote' c

    
-- An example definition of a record: We define that any type is
-- isomorphic to itself. The braces and semicolons are required
-- in this case.
Iso-refl : {A : Set} → Iso A A
Iso-refl = record {
    from    = id
  ; to      = id
  ; from-to = refl
  ; to-from = refl
  }


record usefulProofs : Set₁ where
  field
    isin : {c : Col} → isIn 0 (length (constructors (dt (definition (quote Col)) tt))) (cons2name c) (constructors (dt (definition (quote Col)) tt))
  
-- will need something like a record with the necessary proofs (like isIn)
Iso-Col-Fin : {up : usefulProofs} → Iso (Col) (Fin 3)
Iso-Col-Fin {up} = record {
    from    = λ c → mappingFrom c {usefulProofs.isin up {c}}
  ; to      = mappingTo
  ; from-to = {!refl!}
  ; to-from = {!!}
    }
