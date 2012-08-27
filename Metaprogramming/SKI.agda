open import Equal
open import Reflection
open import Data.Maybe

module SKI (U : Set) (equal? : (x : U) → (y : U) → Equal? x y) (type? : Name → Maybe U) (Uel : U → Set) (quoteVal : (x : U) → Term → Uel x) (quoteBack : (x : U) → Uel x → Term) where

open import Relation.Nullary.Core
open import Data.Bool hiding (T) renaming (_≟_ to _≟Bool_) 
open import Reflection
open import Data.Nat renaming (_≟_ to _≟-Nat_)

open import Data.Stream using (Stream ; evens ; odds ; _∷_ )
open import Coinduction
open import Data.Maybe
open import Data.Empty
open import Data.Product hiding (map)
open import Data.Unit hiding (_≤_; _≤?_)
open import Relation.Binary.PropositionalEquality
open import Data.String renaming (_++_ to _+S+_)
open import Data.Fin hiding (_+_ ; _<_; _≤_ ; suc ; zero) renaming (compare to fcompare)
open import Data.List

-- open import ExampleUniverse

-- open import Datatypes
-- open import TypeCheck
import Datatypes
open module DT = Datatypes U equal? Uel
--open DT --  = Datatypes U equal?
-- import TypeCheck
--open TC -- = TypeCheck U equal? type? {!!}
import TypeCheck
open module TC = TypeCheck U equal? type? Uel quoteVal quoteBack


module SKI where

open import Data.Nat

NamedCtx : Set
NamedCtx = List (ℕ × U')


-- inspiration : http://code.haskell.org/~dolio/

-- new idea: give Comb a notion of environments.

data Comb : (Γ : NamedCtx) → U' → Set where
  Var    : forall {Γ}        → (τ : U') → (n : ℕ) → (n , τ) ∈ Γ → Comb Γ τ
  _⟨_⟩   : forall {Γ σ τ}    → Comb Γ (σ => τ) → Comb Γ σ → Comb Γ τ
  S      : forall {Γ A B C}  → Comb Γ ((A => B => C) => (A => B) => A => C)
  K      : forall {Γ A B}    → Comb Γ (A => B => A)
  I      : forall {Γ A}      → Comb Γ (A => A)
  Lit    : forall {Γ} {x} → Uel x → Comb Γ (O x) -- a constant



lambda : {σ τ : U'}{Γ : NamedCtx} → (n : ℕ) → (c : Comb ((n , σ) ∷ Γ) τ) → (Comb Γ (σ => τ))
lambda          x (Lit l)    = K ⟨ Lit l ⟩
lambda          x S          = K ⟨ S ⟩
lambda          x K          = K ⟨ K ⟩
lambda          x I          = K ⟨ I ⟩
lambda {σ} x (Var .σ .x here) = I
lambda {σ} {τ} x (Var .τ n (there i)) = K ⟨ Var τ n i ⟩
lambda x (t ⟨ t₁ ⟩) = let l1 = lambda x t
                          l2 = lambda x t₁
                      in S ⟨ l1 ⟩ ⟨ l2 ⟩

data NamedWT : (Γ : NamedCtx) → U' -> Set where
  Var   : forall {Γ} {τ} → (n : ℕ)  → (n , τ) ∈ Γ → NamedWT Γ τ
  _⟨_⟩  : forall {Γ} {σ τ} → NamedWT Γ (σ => τ) → NamedWT Γ σ → NamedWT Γ τ
  Lam   : forall {Γ} {τ} → (x : ℕ) → (σ : U') → NamedWT ((x , σ) ∷ Γ) τ → NamedWT Γ (σ => τ)
  Lit   : forall {Γ} {x} → Uel x → NamedWT Γ (O x) -- a constant

compile : (Γ : NamedCtx) → (τ : U') → NamedWT Γ τ → (Comb Γ τ)
compile Γ (O σ) (Lit x) = Lit x
compile Γ τ (Var n h) = Var τ n h
compile Γ τ (_⟨_⟩ {.Γ}{σ} wt wt₁) = compile Γ (σ => τ) wt ⟨ compile Γ σ wt₁ ⟩
compile Γ (σ => τ) (Lam x .σ wt) = lambda x (compile ((x , σ) ∷ Γ) τ wt) 
  
topCompile : {τ : U'} → NamedWT [] τ → Comb [] τ
topCompile (Lit x) = Lit x
topCompile (Var n ())
topCompile {τ}(nwt ⟨ nwt₁ ⟩)      = compile [] τ (nwt ⟨ nwt₁ ⟩)
topCompile {.σ => τ}(Lam x σ nwt) = compile [] (σ => τ) (Lam x σ nwt)

  
open import Data.Vec hiding (_∈_)

Substitution : ℕ → Set
Substitution n = Vec ℕ n

sub : (c : Ctx) → Substitution (length c) → NamedCtx
sub [] [] = []
sub (x ∷ subs) (x₁ ∷ ctx) = (x₁ , x) ∷ sub subs ctx


coerce∈ : forall {τ} → (Γ : Ctx) → (s : Substitution (length Γ)) → (idx : τ ∈ Γ) → (lookup (finindex idx) s , τ) ∈ sub Γ s
coerce∈ {τ} .(τ ∷ []) sub (here {[]}) with sub
coerce∈ {τ} .(τ ∷ []) sub (here {[]}) | x ∷ [] = here -- force Agda to notice sub is 1 long.
coerce∈ {τ} .(τ ∷ x ∷ xs) sub (here {x ∷ xs}) with sub
coerce∈ {τ} .(τ ∷ xs ∷ sub) xs (here {sub ∷ x₁}) | x ∷ x₂ ∷ a = here -- same story, but sub has length of Γ
coerce∈ .(y ∷ xs) sub (there {xs} {y} idx) with sub
coerce∈ .(y ∷ xs) xs (there {y} idx) | x ∷ a = there (coerce∈ y a idx)

unbrown' : forall {σ} → (Γ : Ctx) → FreshVariables → (s : Substitution (length Γ)) → WT Γ σ → NamedWT (sub Γ s) σ
unbrown' Γ (f ∷ fs) sub (Var x)      = Var (lookup (finindex x) sub) (coerce∈ Γ sub x)
unbrown' Γ (f ∷ fs) sub (wt ⟨ wt₁ ⟩) = unbrown' Γ (evens (♭ fs)) sub wt ⟨ unbrown' Γ (odds (♭ fs)) sub wt₁ ⟩
unbrown' Γ (f ∷ fs) sub (Lam σ wt)   = Lam f σ (unbrown' (σ ∷ Γ) (♭ fs) (f ∷ sub) wt)
unbrown' Γ (f ∷ fs) sub (Lit x)      = Lit x

unbrown : {σ : U'} → WT [] σ → NamedWT [] σ
unbrown = unbrown' [] fv []

flatten : NamedCtx → Ctx
flatten [] = []
flatten ((n , σ) ∷ xs) = σ ∷ flatten xs

coerce∋ : forall {n τ} → (Γ : NamedCtx) → (idx : (n , τ) ∈ Γ) → (τ ∈ flatten Γ)
coerce∋ {n} {τ} .((n , τ) ∷ xs) (here {xs}) = here
coerce∋ .(y ∷ xs) (there {xs} {y} idx)      = there (coerce∋ xs idx)

brown : forall {σ} → (Γ : NamedCtx) → NamedWT Γ σ → WT (flatten Γ) σ
brown Γ (Lit x)      = Lit x
brown Γ (Var n x)    = Var (coerce∋ Γ x)
brown Γ (wt ⟨ wt₁ ⟩) = (brown Γ wt) ⟨ brown Γ wt₁ ⟩
brown Γ (Lam x σ wt) = Lam σ (brown ((x , σ) ∷ Γ) wt)

private

    noVar : {τ : U'} → {Γ : NamedCtx} → Comb Γ τ → Set
    noVar (Lit x) = ⊤
    noVar (Var τ x i) = ⊥
    noVar (_⟨_⟩ c c₁) = noVar c × noVar c₁
    noVar S = ⊤
    noVar K = ⊤
    noVar I = ⊤

    closed→closed : {σ : U'} → (x : Comb [] σ) → noVar x
    closed→closed (Lit x) = tt
    closed→closed {σ} (Var .σ n ())
    closed→closed (v ⟨ v₁ ⟩) = (closed→closed v) , (closed→closed v₁)
    closed→closed S = tt
    closed→closed K = tt
    closed→closed I = tt


Srep : ∀ {A B C Γ} → WT Γ ((A => B => C) => (A => B) => A => C)
Srep {A}{B}{C} = Lam (A => B => C) (Lam (A => B) (Lam A
                      ( Var (there (there here)) ⟨ Var here ⟩ ⟨ (Var (there here)) ⟨ (Var here) ⟩ ⟩ )))

Irep : ∀ {A Γ} → WT Γ (A => A)
Irep {A} = Lam A (Var here)

Krep : ∀ {A B Γ} → WT Γ (A => B => A)
Krep {A}{B} = Lam A (Lam B (Var (there here)))

ski2wt : {Γ : NamedCtx} {σ : U'} → Comb Γ σ → WT (flatten Γ) σ
ski2wt {Γ} {σ} (Var .σ n h) = Var (coerce∋ Γ h)
ski2wt (c ⟨ c₁ ⟩) = ski2wt c ⟨ ski2wt c₁ ⟩
ski2wt S = Srep
ski2wt K = Krep
ski2wt I = Irep
ski2wt (Lit x₁) = Lit x₁

open import ConcreteSKI
open import Apply

ski2term : {σ : U'} → Comb [] σ → Term
ski2term {O σ} (Lit x) = quoteBack σ x
ski2term {σ} (Var .σ n ())
ski2term (c ⟨ c₁ ⟩) = lam visible pleaseinfer (lam visible pleaseinfer (var 1 (arg visible relevant (var 0 []) ∷ [])))
ski2term {(a => b => c) => (.a => .b) => .a => .c} S =      lam visible pleaseinfer (
                                                               lam visible pleaseinfer (
                                                                  lam visible pleaseinfer (def (quote s) (
                                                                       arg visible relevant (var 2 []) ∷
                                                                       arg visible relevant (var 1 []) ∷
                                                                       arg visible relevant (var 0 []) ∷ []))))
ski2term {a => b => .a} K   = lam visible pleaseinfer (
                                 lam visible pleaseinfer (def (quote k) (
                                     arg visible relevant (var 1 []) ∷
                                     arg visible relevant (var 0 []) ∷ [])))
ski2term {a => .a} I        = lam visible pleaseinfer (def (quote i) (
                                 arg visible relevant (var 0 []) ∷ []))

ski2type : {σ : U'} → Comb [] σ → Set
ski2type {σ} c = el' σ

-- alternative; this is shorter.
ski2term' : {σ : U'} → Comb [] σ → Term
ski2term' c = lam2term (ski2wt c) 


{-
open import Relation.Binary

Renaming : Set
Renaming = List (from × to)
  where from = ℕ
        to   = ℕ

find : {A B : Set}{d : Decidable {A = A} _≡_} → List (A × B) → A → Maybe B
find {_}{_}{d} []             k = nothing
find {_}{_}{d} ((x , y) ∷ xs) k with d x k
find {_}{_}{d}((x , y) ∷ xs) k | yes p = just y
find {_}{_}{d}((x , y) ∷ xs) k | no ¬p = find {d = d} xs k

ren : ∀ {Γ σ} → Renaming → NamedWT Γ σ → Maybe (NamedWT Γ σ)
ren r (Var n x)    with find {d = _≟-Nat_} r n
ren r (Var n x₁) | just x = {!just (Var x x₁)!}
ren r (Var n x) | nothing = nothing
ren r (wt ⟨ wt₁ ⟩) with ren r wt | ren r wt₁
ren r (wt ⟨ wt₁ ⟩) | just x | just x₁ = just (x ⟨ x₁ ⟩)
ren r (wt ⟨ wt₁ ⟩) | just x | nothing = nothing
ren r (wt ⟨ wt₁ ⟩) | nothing | b = nothing
ren r (Lam x σ wt) with ren r wt | r ! x
ren r (Lam .(index p) σ wt) | just x₁ | inside (from , to) p = {!!}
ren r (Lam .(length r + m) σ wt) | just x₁ | outside m = {!!} -- just (Lam {!!} σ x₁)
ren r (Lam x σ wt) | nothing | a = nothing

data _~_ {σ : U'} : NamedWT [] σ → NamedWT [] σ → Set where
  nwt-eq : ∀ {e₁ e₂} → (s : Renaming) → ren s e₁ ≡ just e₂ → e₁ ~ e₂

_≈_ : {σ : U'} → NamedWT [] σ → NamedWT [] σ → Set
_≈_ a b = {!!}

wtsetoid : {σ : U'} → NamedWT [] σ → Setoid {!!} {!!}
wtsetoid {σ} wt = record {
  Carrier = NamedWT [] σ
  ; _≈_ = _≈_
  ; isEquivalence = record {
        refl = {!!}
      ; sym = {!!}
      ; trans = {!!}
     }
  }

-- We capture that two sets are isomorphic using the following record.
record Iso (A B : Set) : Set where
  field
    from    : A → B
    to      : B → A
    from-to : {x : B} → from (to x) ≡ x
    to-from : {x : A} → to (from x) ≡ x

open import Relation.Binary.EqReasoning


cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v m n} → x ≡ y → u ≡ v → m ≡ n → f x u m ≡ f y v n
cong₃ f refl refl refl = refl

-- de Bruijn and named aren't 100% isomorphic; taking a random
-- named lambda and doing debruijn translataion then back might give
-- different "fresh" variables. this is why we can only prove one direction
-- of the isomorphism; either that or use setoids, where we can build in alpha-equivalence

fromto : {σ : U'} → (fv' : FreshVariables) → (x : NamedWT [] σ) → unbrown' [] fv' [] (brown [] x) ≡ x
fromto (f ∷ fs) (Var n ())
fromto (f ∷ fs) (x ⟨ x₁ ⟩) = cong₂ _⟨_⟩ (fromto (evens (♭ fs)) x) (fromto (odds (♭ fs)) x₁) 
fromto (f ∷ fs) (Lam x σ x₁) = cong₃ (λ x₂ σ₁ x₃ → Lam x₂ σ {!!}) {!!} {!!} {!!}



--                                                                                 
open import Level hiding (suc)                                                                    
open import Relation.Binary
open import Relation.Binary.PropositionalEquality


 -- Small-step reduction of lambda calculus                                    
infixl 4 _⟶_                                                                  
                                                                              
data _⟶_ {Γ : Ctx}{σ : U'} : WT Γ σ → WT Γ σ → Set where                                  
--  left  : {t₁ t₂ t : WT Γ σ} →                                                 
--          t₁ ⟶ t₂ → t₁ ! t ⟶ t₂ ! t                                           
--  right : {t₁ t₂ t : WT Γ σ} →                                                 
--          t₁ ⟶ t₂ → t ! t₁ ⟶ t ! t₂                                           
--  lam   : {t₁ t₂   : WT Γ σ} →                                            -- wrong
--          t₁ ⟶ t₂ → lam t₁ ⟶ lam t₂                                           
--  beta  : {t₁ : Lam (suc n)} {t₂ : Lam n} →                                   
--          lam t₁ ! t₂ ⟶ β t₁ t₂    

--   open LambdaCalculus                                                           
--                                                                                 
--   -- Define the reflexive, symmetric, transitive closure of                     
--   -- a relation, i.e., given a relation R, the relation Closure R               
--   -- should be the smallest equivalence relation that contains R.               
--   -- Ignore the zero argument to the Rel type. That's related                   
--   -- to universe polymorphism again, and the reason we import                   
--   -- Level above.                                                               
data Closure {I : Set} (R : Rel I Level.zero) : Rel I Level.zero where                    
  bse   : {x y : I} → R x y → Closure R x y                                    
  rfl   : Reflexive  (Closure R)                                             
  sm    : Symmetric  (Closure R)                                             
  trns  : Transitive (Closure R)                                             
--                                                                                 
--                                                                                 
--   -- We can now define the convertibility relation to be the                    
--   -- closure of the small-step reduction in lambda calculus.                    
--infixl 3 _⟷_                                                                  
--                                                                                 
--_⟷_ : {n : ℕ} → Rel (Lam n) _                                                 
--_⟷_ = Closure _⟶_                                                             
--                                                                                 
--   -- There is some "yellow" below. This is going                                
--   -- to disappear when you define the functions.                                
--                                                                                 
--   -- Define a setoid for lambda terms.                                          
-- lamSetoid : {n : ℕ} → Setoid _ _                                              
-- lamSetoid {n} = record {                                                      
--               Carrier       = Lam n;                                          
--               _≈_           = _⟷_;                                            
--               isEquivalence = record {                                       
--                                 refl  = refl                                  
--                               ; sym   = sym
--                               ; trans = trans
--                               }
--              }                                                                
--                                                                                 
--                                                                                 
--   -- Prove that the identity combinator actually behaves like the               
--   -- the identity.                                                              
--   -- NOT FOR GRADING, JUST FOR FUN.                                             
--   I-identity : (t : Lam 0) → I ! t ⟷ t                                          
--   I-identity = {!!}                                                             
--                                                                                 
--   -- Prove that I can be expressed in terms of S and K.                         
--   -- NOT FOR GRADING, JUST FOR FUN.                                             
--   SK-I : (t : Lam 0) → S ! K ! t ⟷ I                                            
--   SK-I t = {!!}                                                                 
--                                                                                 
--   -- Prove using convertibility reasoning that Y is a fixed-point               
--   -- combinator.                                                                
--   Y-fixed : ∀ f → Y ! f ⟷ f ! (Y ! f)                                           
--   Y-fixed f =                                                                   
--     let                                                                         
--       open Relation.Binary.EqReasoning lamSetoid                                
--         renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)                                             
--     in                                                                          
--       begin.                                                                    
--         Y ! f                                                                   
--       ⟷⟨ refl ⟩                                                                 
--         lam (lam (v 1 ! (v 0 ! v 0)) ! lam (v 1 ! (v 0 ! v 0))) ! f             
--         ⟷⟨ base (left (lam beta)) ⟩                                             
--         lam (v 0 ! (lam (v 1 ! (v 0 ! v 0)) ! lam (v 1 ! (v 0 ! v 0)))) ! f     
--         ⟷⟨ base beta ⟩                                                          
--           f ! (lam (lf zero f ! (var Data.Fin.zero ! var Data.Fin.zero)) !      
--              lam (lf zero f ! (var Data.Fin.zero ! var Data.Fin.zero)))         
--       ⟷⟨ sym (base (right beta)) ⟩                                              
--         f ! (lam (lam (v 1 ! (v 0 ! v 0)) ! lam (v 1 ! (v 0 ! v 0))) ! f).      
--       ⟷⟨ refl ⟩                                                                 
--         f ! (Y ! f)                                                             
--       ∎                                              


tofrom : {σ : U'} → (fv' : FreshVariables) → (x : WT [] σ) → brown [] (unbrown' [] fv' [] x) ≡ x
tofrom (f ∷ fs) (Var ())
tofrom (f ∷ fs) (wt ⟨ wt₁ ⟩) = cong₂ _⟨_⟩ (tofrom (evens (♭ fs)) wt) (tofrom (odds (♭ fs)) wt₁)
tofrom (f ∷ fs) (Lam σ wt) = cong₂ {!\ x y → Lam!} {!!} {!!} 


deBruijnIso : {σ : U'} → Iso (WT [] σ) (NamedWT [] σ)
deBruijnIso = record {
    from = unbrown' [] fv []
  ; to   = brown []
  ; from-to = λ {x} → fromto fv x
  ; to-from = {!!}
  }

-}
