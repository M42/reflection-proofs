\documentclass{beamer}

\usetheme{Warsaw}
\setbeamertemplate{itemize items}[default]
\setbeamertemplate{enumerate items}[default]
\usecolortheme{bordeaux}


%include polycode.fmt
%if style == newcode
%else
%include agda.fmt
%include codecolour.fmt
%include generated-colour.fmt
%endif

\newcommand{\ignore}[1]{}

\ignore{
\begin{code}
module ReflectionProofs where
\end{code}


\begin{code}
-- imports for Evenness
open import Relation.Binary.PropositionalEquality
open import Data.Bool renaming (not to ¬_)
open import Data.Nat
\end{code}
}

\ignore{
\begin{code}
-- imports for Boolean tauto solver
open import Data.String
open import Relation.Nullary hiding (¬_)
open import Data.Product hiding (map)
open import Relation.Binary hiding (_⇒_)
open import Reflection

open import Data.Fin hiding (_+_; pred)
open import Data.Vec renaming (reverse to vreverse ; map to vmap; foldr to vfoldr; _++_ to _v++_)
open import Data.Unit hiding (_≤?_)
open import Data.Empty
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.List hiding (_∷ʳ_)
\end{code}
}

\usepackage{amsmath}
\usepackage{semantic}
% things for the semantic package
\reservestyle{\command}{\textbf}
\command{let,in,:,case,of,if,then,else,letrec,nil,cons,false,true,[]}
\mathlig{ -->}{\longrightarrow}


\usepackage{url}

\author{Paul van der Walt \and Wouter Swierstra}
\date{July 4, 2012}
\title{Proof by reflection by reflection}
\institute{\url{paul@@denknerd.org}, \url{W.S.Swierstra@@uu.nl}\\
Department of Computer Science, Utrecht University
}

\begin{document}

\maketitle




\section{Introduction}

\begin{frame}


\tableofcontents

\end{frame}

\begin{frame}



\end{frame}
\section{Crash-course on Dependently Typed Programming}

\begin{frame}
\begin{itemize}
    \item In Haskell/ML: clear separation types vs. values
    \item Example:
\end{itemize}
\begin{code}
fac : ℕ → ℕ
fac 0          = 1
fac (suc n)    = (suc n) * fac n
\end{code}
\end{frame}

\begin{frame}
    \begin{itemize}
        \item In DTP, types may depend on values
        \item Profound implications
        \item Usual example: | Vec A n |
        \item |n| may be arbitrary value, unkown at compile-time
            \pause
        \item We can encode proofs as values; use them as type arguments
        \item Eg: |isEven 6 == true|
    \end{itemize}
\end{frame}

\begin{frame}
    \begin{itemize}
        \item Therefore, DTP can be used as a logic
        \item Interlude: what is intuitionistic logic?
            \pause
        \item We must require \alert{total}, \alert{terminating} functions
        \item Why? Total: implies no crashes, functions are defined on all inputs
        \item Terminating: we may not prove |false|
    \end{itemize}
\begin{code}
nonsense : ⊥
nonsense = nonsense
\end{code}
\begin{spec}
falsity : ⊥ -> Anything
\end{spec}
\end{frame}

\begin{frame}
    \begin{itemize}
        \item Simple example of dependent type
    \end{itemize}
\begin{code}
data Vec' (A : Set) : ℕ → Set  where
  []       : Vec' A zero
  _∷_      : {n : ℕ} → A → Vec' A n → Vec' A (suc n)
\end{code}
\begin{itemize}
    \item A number of interesting things here
    \item |Vec A| is a family of types, indexed by naturals
    \item For each $n$, |Vec A n| is a type
    \item $\Rightarrow$ lists with differing lengths have different types
\end{itemize}
\end{frame}


\begin{frame}
    \begin{itemize}
        \item This makes pattern-matching more interesting
        \item Head of non-empty list (note: crashes in Haskell)
    \end{itemize}
\begin{code}
head' : {n : ℕ} {A : Set} → Vec' A (suc n) → A
head' (x ∷ xs) = x
\end{code}
\begin{itemize}
    \item Now, if we try |head []| we get a type-error at compile-time
\end{itemize}
\end{frame}

\begin{frame}
    \begin{itemize}
        \item Coq (INRIA et al) and Agda (Chalmers) are implementations of constructive logic using dependent types
            \pause
        \item My project: explore reflection API (new since Agda 2.2.8)
        \item Document it properly
        \item Give neat examples of how it can be used
            \pause
        \item Question: what can we automate? Is the reflection system powerful enough?
        \item Intro definitions by unquoting not yet possible
        \item Inspect functions and their cases also not yet possible
    \end{itemize}
\end{frame}

\section{Proof by Reflection}

\begin{frame}

    \begin{block}{Note}
        Has nothing to do with programming language reflection (quote / unquote and friends).
    \end{block}
\pause
    Idea behind proof by reflection:
    \begin{itemize}
        \item Don't construct direct proof (derivation tree) for each instance
        \item Define an algorithm to generate proofs for instances
        \item 2 case studies follow
    \end{itemize}

\end{frame}







\subsection{Simple Example: Evenness}

\begin{frame}{Case study: even naturals}
    \begin{itemize}
        \item Example: property of evenness on naturals ($[0 .. n]$)
        \item Property is defined using two rules
        \item Proofs can become cumbersome
    \end{itemize}


    \begin{center}
        \begin{tabular}{ccc}
            \inference[zero-even]{}{|Even 0|}\label{evenzero} & ~~~ & \inference[ss-even]{|Even n|}{|Even (suc (suc n))|}\label{evenss}
        \end{tabular}
    \end{center}
\end{frame}


\begin{frame}[fragile]
    \begin{itemize}
        \item Translation of rules into Agda datatype
    \end{itemize}
\begin{code}
data Even      : ℕ → Set where
  isEvenZ      :                          Even 0
  isEvenSS     : {n : ℕ} → Even n     →   Even (2 + n)
\end{code}
\end{frame}

\begin{frame}[fragile]
    \begin{itemize}
        \item This is an example of a proof in Agda
        \item Producing derivation tree each time is painful
    \end{itemize}
\begin{code}
isEven6 : Even 6
isEven6 = isEvenSS (isEvenSS (isEvenSS isEvenZ))
\end{code}
\begin{itemize}
    \item Solution: proof by reflection
\end{itemize}
\end{frame}



\begin{frame}
    \begin{itemize}
        \item Proof by reflection: a proof algorithm
        \item Step 1: define a decision function
        \item Direct translation of rules
    \end{itemize}

\begin{code}
even? : ℕ → Bool
even? 0              = true
even? 1              = false
even? (suc (suc n))  = even? n
\end{code}
\end{frame}

\begin{frame}
    \begin{itemize}
        \item Step 2: prove the soundness of decision function
        \item i.e. if decision function returns |true| for some $n$, show that
            |Even n| holds
    \end{itemize}
\begin{code}
soundnessEven : {n : ℕ} → even? n ≡ true → Even n
soundnessEven {0}              refl        = isEvenZ
soundnessEven {1}              ()
soundnessEven {suc (suc n)}    s           = isEvenSS (soundnessEven s)
\end{code}
\begin{itemize}
    \item Looking closely, this is the (structural) algorithm for a direct proof like |isEven6|
\end{itemize}
\end{frame}


\begin{frame}
    \begin{itemize}
        \item Now any proof that some $n$ is |Even| is easy
        \item All that's needed is |even? n ≡ true|, then it's proven
        \item Agda trick (thanks to $\beta$-reduction in type system):
    \end{itemize}
\begin{code}
isEven28        : Even 28
isEven28        = soundnessEven {28} refl

isEven8772      : Even 8772
isEven8772      = soundnessEven refl
\end{code}
\begin{itemize}
    \item Note that for some $n$ which is uneven, we cannot prove |Even n|.
        The proof obligation reduces to |true ≡ false| in this case.
    \item We can even hide the |refl| (skipped)
\end{itemize}
\end{frame}

% \begin{frame}
% \begin{code}
% Oh : Bool → Set
% Oh true    = ⊤
% Oh false   = ⊥
% 
% soundEven : {n : ℕ} → {oh : Oh (even? n)} → Even n
% soundEven {zero}              {tt}   = isEvenZ
% soundEven {suc zero}          {()}   -- absurd
% soundEven {suc (suc n)}       {oh}   = isEvenSS (soundEven {n} {oh})
% 
% isEven12     : Even 12
% isEven12     = soundEven
% \end{code}
% \end{frame}
% 
% 
% \begin{frame}{Why the implicit arguments work}
%     \begin{itemize}
%         \item Agda can automatically instantiate simple record types (this is safe)
%         \item Decision tree is a nested pair of |⊤|-values
%         \item Unless the natural isn't even, in which case no value can be constructed
%     \end{itemize}
% 
% \begin{code}
% foo : {u : ⊤ × ⊤} → ℕ
% foo = 5
% 
% baz : ℕ
% baz = foo
% \end{code}
% \end{frame}


\subsection{Second Example: Boolean Tautologies}

\begin{frame}
    \begin{itemize}
        \item Second example: boolean tautologies
        \item An example: Eqn. \ref{eqn:tauto-example}
\begin{align}\label{eqn:tauto-example}
(p_1 \vee q_1) \wedge (p_2 \vee q_2) \Rightarrow (q_1 \vee p_1) \wedge (q_2 \vee p_2)
\end{align}
        \item Tedious to prove by hand
        \item Trying all variable assignments requires $2^n$ cases
            \pause
        \item Outline:
            \begin{itemize}
                \item Express actual formula in some abstract way
                    \pause
                \item Decide properties on the abstract representation
                    \pause
                \item Prove soundness of decision
                    \pause
                \item ``Reflect''\footnote{In proof-by-reflection sense.} abstract representation back to (concrete) proof obligation
                    \pause
                \item Call |soundness| for each term
            \end{itemize}
    \end{itemize}
\end{frame}


\begin{frame}
    \begin{itemize}
        \item First step: define abstract representation
        \item |Atomic| stands for an arbitrary unknown formula
        \item |Atomic|'s argument is a de Bruijn index \textcolor{gray}{(|Fin| ensures variables are bound)}
    \end{itemize}
\begin{code}
data BoolExpr : ℕ → Set where
  Truth         : {n : ℕ}                                → BoolExpr n
  Falsehood     : {n : ℕ}                                → BoolExpr n
  And           : {n : ℕ} → BoolExpr n → BoolExpr n      → BoolExpr n
  Or            : {n : ℕ} → BoolExpr n → BoolExpr n      → BoolExpr n
  Not           : {n : ℕ} → BoolExpr n                   → BoolExpr n
  Imp           : {n : ℕ} → BoolExpr n → BoolExpr n      → BoolExpr n
  Atomic        : {n : ℕ} → Fin n                        → BoolExpr n
\end{code}
\end{frame}


\ignore{
\begin{frame}
    \begin{itemize}
        \item Also needed: mapping from variables to assignments
        \item Call this |Env n|
    \end{itemize}

\begin{code}
Env   : ℕ  → Set
Env   = Vec Bool
\end{code}
\end{frame}

}

\ignore{
\begin{code}
infixr 4 _⇒_
_⇒_ : Bool → Bool → Bool
true  ⇒ true  = true
true  ⇒ false = false
false ⇒ true  = true
false ⇒ false = true
\end{code}
}


\begin{frame}

    \begin{itemize}
        \item Decision (=interpretation) function is unsurprising
        \item Needs environment for free variables
    \end{itemize}

\begin{code}
⟦_⊢_⟧ : ∀ {n : ℕ} (e : Env n) → BoolExpr n → Bool
⟦ env     ⊢ Truth       ⟧ = true
⟦ env     ⊢ Falsehood   ⟧ = false
⟦ env     ⊢ And be be₁  ⟧ =     ⟦ env ⊢ be ⟧     ∧      ⟦ env ⊢ be₁ ⟧
⟦ env     ⊢ Or be be₁   ⟧ =     ⟦ env ⊢ be ⟧     ∨      ⟦ env ⊢ be₁ ⟧
⟦ env     ⊢ Not be      ⟧ = ¬   ⟦ env ⊢ be ⟧
⟦ env     ⊢ Imp be be₁  ⟧ =     ⟦ env ⊢ be ⟧     ⇒      ⟦ env ⊢ be₁ ⟧
⟦ env     ⊢ Atomic n    ⟧ = lookup n env
\end{code}

\end{frame}


\begin{frame}
    \begin{itemize}
        \item Before actually proving soundness of this function, some helpers are needed
        \item |So| maps |true| to |⊤| and |false| to |⊥|
    \end{itemize}
\begin{code}

data Error (a : String) : Set where

So : String → Bool → Set
So _ true  = ⊤
So s false = Error s

P : Bool → Set
P = So "expression isn't true"
\end{code}
\end{frame}


\begin{frame}
    \begin{itemize}
        \item To express a tautology we now write
        \item Note proof: case for each possible assignment
        \item This repetition must be abstracted away
    \end{itemize}
\begin{code}
b⇒b : (b : Bool) → P(b ⇒ b)
b⇒b true  = tt
b⇒b false = tt

t1 : Set
t1 = (p1 q1 p2 q2 : Bool)   →   P  (      (p1 ∨ q1) ∧ (p2 ∨ q2)
                                      ⇒   (q1 ∨ p1) ∧ (q2 ∨ p2)
                                   )
\end{code}
\vskip -5mm
\begin{spec}
pf : t1
pf = (HOLE 0)
\end{spec}
\end{frame}




\ignore{
\begin{code}
data Diff : ℕ → ℕ → Set where
  Base : ∀ {n}   → Diff n n
  Step : ∀ {n m} → Diff (suc n) m → Diff n m
\end{code}

\begin{code}
freeVars : Term → ℕ
freeVars (pi (arg visible relevant (el (lit _) (def Bool []))) (el s t)) = suc (freeVars t)
freeVars (pi a b)     = 0
freeVars (var x args) = 0
freeVars (con c args) = 0
freeVars (def f args) = 0
freeVars (lam v t)    = 0
freeVars (sort x)     = 0
freeVars unknown      = 0

-- peels off all the outermost Pi constructors,
-- returning a term with freeVars free variables.

stripPi : Term → Term
stripPi (pi (arg visible relevant (el (lit _) (def Bool []))) (el s t)) = stripPi t
-- identity otherwise
stripPi (pi args t)  = pi   args t
stripPi (var x args) = var  x    args
stripPi (con c args) = con  c    args
stripPi (def f args) = def  f    args
stripPi (lam v t)    = lam  v    t
stripPi (sort x)     = sort x
stripPi unknown      = unknown

-- TODO get rid of this!
unsafeMinus : (a : ℕ) → (b : ℕ) → ℕ
unsafeMinus zero m = zero
unsafeMinus n₁ zero = n₁
unsafeMinus (suc n₁) (suc m) = unsafeMinus n₁ m


isSoExprQ : (t : Term) → Set
isSoExprQ (var x args) = ⊥
isSoExprQ (con c args) = ⊥
isSoExprQ (def f args) with Data.Nat._≟_ (length args) 2
isSoExprQ (def f args) | yes p with tt
isSoExprQ (def f [])                        | yes () | tt
isSoExprQ (def f (x ∷ []))                  | yes () | tt
isSoExprQ (def f (a ∷ arg v r x ∷ []))      | yes p  | tt with f ≟-Name quote So
isSoExprQ (def f (a ∷ arg v r x ∷ [])) | yes p₁ | tt | yes p = ⊤
isSoExprQ (def f (a ∷ arg v r x ∷ [])) | yes p | tt | no ¬p = ⊥
isSoExprQ (def f (x ∷ x₃ ∷ x₄ ∷ args))      | yes () | tt
isSoExprQ (def f args)                      | no ¬p with tt
isSoExprQ (def f [])                        | no ¬p | tt = ⊥
isSoExprQ (def f (x ∷ xs))                  | no ¬p | tt = ⊥
isSoExprQ (lam v t)                         = ⊥
isSoExprQ (pi t₁ t₂)                        = ⊥
isSoExprQ (sort x)                          = ⊥
isSoExprQ unknown                           = ⊥


stripSo : (t : Term) → isSoExprQ t → Term
stripSo (var x args) ()
stripSo (con c args) ()
stripSo (def f args) pf with Data.Nat._≟_ (length args) 2
stripSo (def f args) pf | yes p with tt
stripSo (def f [])   pf                      | yes () | tt
stripSo (def f (x ∷ [])) pf                  | yes () | tt
stripSo (def f (a ∷ arg v r x ∷ [])) pf      | yes p  | tt with f ≟-Name quote So
stripSo (def f (a ∷ arg v r x ∷ [])) pf  | yes p₁ | tt | yes p = x
stripSo (def f (a ∷ arg v r x ∷ [])) () | yes p | tt | no ¬p
stripSo (def f (x ∷ x₃ ∷ x₄ ∷ args)) pf     | yes () | tt
stripSo (def f args)             pf         | no ¬p with tt
stripSo (def f []) () | no ¬p | tt
stripSo (def f (x ∷ xs)) () | no ¬p | tt
stripSo (lam v t)    ()
stripSo (pi t₁ t₂)   ()
stripSo (sort x)     ()
stripSo unknown      ()


isBoolExprQ' : (n : ℕ) → (t : Term) → Set
isBoolExprQ' n (var x args) with suc (unsafeMinus x 0) ≤? n
isBoolExprQ' n (var x args) | yes p = ⊤
isBoolExprQ' n (var x args) | no ¬p = ⊥
isBoolExprQ' n (con tf as) with Data.Nat._≟_ 0 (length as)
isBoolExprQ' n (con tf []) | yes pp with tf ≟-Name quote true
isBoolExprQ' n (con tf []) | yes pp | yes p = ⊤
isBoolExprQ' n (con tf []) | yes pp | no ¬p with tf ≟-Name quote false
isBoolExprQ' n (con tf []) | yes pp | no ¬p  | yes p = ⊤
isBoolExprQ' n (con tf []) | yes pp | no ¬p₁ | no ¬p = ⊥
isBoolExprQ' n (con tf (x ∷ as)) | yes ()
isBoolExprQ' n (con tf []) | no ¬p = ⊥-elim (¬p refl)
isBoolExprQ' n (con tf (a ∷ s)) | no ¬p = ⊥
isBoolExprQ' n (def f []) = ⊥
isBoolExprQ' n (def f (arg v r x ∷ [])) with f ≟-Name quote ¬_
isBoolExprQ' n (def f (arg v r x ∷ [])) | yes p = isBoolExprQ' n x
isBoolExprQ' n (def f (arg v r x ∷ [])) | no ¬p = ⊥
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) with f ≟-Name quote _∧_
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | yes p = (isBoolExprQ' n x) × (isBoolExprQ' n x₁)
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | no ¬p with f ≟-Name quote _∨_
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | no ¬p | yes p = (isBoolExprQ' n x) × (isBoolExprQ' n x₁)
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | no ¬p₁ | no ¬p with f ≟-Name quote _⇒_
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | no ¬p₁ | no ¬p | yes p = (isBoolExprQ' n x) × (isBoolExprQ' n x₁)
isBoolExprQ' n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | no ¬p₂ | no ¬p₁ | no ¬p = ⊥
isBoolExprQ' n (def f (x ∷ x₁ ∷ x₂ ∷ args)) = ⊥
isBoolExprQ' n (lam v t) = ⊥
isBoolExprQ' n (pi t₁ t₂) = ⊥
isBoolExprQ' n (sort y) = ⊥
isBoolExprQ' n unknown = ⊥

isBoolExprQ : (freeVars : ℕ) → (t : Term) → isSoExprQ t → Set
isBoolExprQ n t pf with stripSo t pf
isBoolExprQ n t pf | t' = isBoolExprQ' n t'

term2boolexpr : (n : ℕ)
        → (t : Term)
        → isBoolExprQ' n t
        → BoolExpr n
term2boolexpr n (var x args) pf with suc (unsafeMinus x 0) ≤? n
term2boolexpr n (var x args) pf | yes p = Atomic (fromℕ≤ {unsafeMinus x 0} p)
term2boolexpr n (var x args) () | no ¬p
term2boolexpr n (con tf []) pf with tf ≟-Name quote true
term2boolexpr n (con tf []) pf | yes p = Truth
term2boolexpr n (con tf []) pf | no ¬p with tf ≟-Name quote false
term2boolexpr n (con tf []) pf | no ¬p  | yes p = Falsehood
term2boolexpr n (con tf []) () | no ¬p₁ | no ¬p
term2boolexpr n (con c (a ∷ rgs)) ()
term2boolexpr n (def f []) ()
term2boolexpr n (def f (arg v r x ∷ [])) pf with f ≟-Name quote ¬_
term2boolexpr n (def f (arg v r x ∷ [])) pf | yes p = Not (term2boolexpr n x pf)
term2boolexpr n (def f (arg v r x ∷ [])) () | no ¬p
term2boolexpr n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) pf with f ≟-Name quote _∧_
term2boolexpr n (def f (arg a₁ b₁ x ∷ arg a b x₁ ∷ [])) (proj₁ , proj₂) | yes p = And
  (term2boolexpr n x proj₁)
  (term2boolexpr n x₁ proj₂)
term2boolexpr n (def f (arg a₁ b₁ x ∷ arg a b x₁ ∷ [])) pf | no p with f ≟-Name quote _∨_
term2boolexpr n (def f (arg a₁ b₁ x ∷ arg a b x₁ ∷ [])) (proj₁ , proj₂) | no ¬p | yes p = Or
  (term2boolexpr n x proj₁)
  (term2boolexpr n x₁ proj₂)
term2boolexpr n (def f (arg a₁ b₁ x ∷ arg a b x₁ ∷ [])) pf | no ¬p | no p with f ≟-Name quote _⇒_
term2boolexpr n (def f (arg a₁ b₁ x ∷ arg a b x₁ ∷ [])) (proj₁ , proj₂) | no ¬p₁ | no ¬p | yes p = Imp
  (term2boolexpr n x proj₁)
  (term2boolexpr n x₁ proj₂)
term2boolexpr n (def f (arg a₁ b₁ x ∷ arg a b x₁ ∷ [])) () | no ¬p | no p | no p₁
term2boolexpr n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ x₂ ∷ args)) ()
term2boolexpr n (lam v t)  ()
term2boolexpr n (pi t₁ t₂) ()
term2boolexpr n (sort x)   ()
term2boolexpr n unknown    ()

zeroId : (n : ℕ) → n ≡ n + 0
zeroId zero                           = refl
zeroId (suc  n) with n + 0 | zeroId n
zeroId (suc .w)    | w     | refl     = refl

succLemma : (n m : ℕ) → suc (n + m) ≡ n + suc m
succLemma zero m    = refl
succLemma (suc n) m = cong suc (succLemma n m)

coerceDiff : {n m k : ℕ} → n ≡ m → Diff k n → Diff k m
coerceDiff refl d = d

zero-least : (k n : ℕ) → Diff k (k + n)
zero-least k zero    = coerceDiff (zeroId k) Base
zero-least k (suc n) = Step (coerceDiff (succLemma k n) (zero-least (suc k) n))

\end{code}

\begin{frame}
    \begin{itemize}
        \item Now we have a representation and a decision
        \item Before proving soundness, relation of abstract to concrete formula is needed
        \item |forallBool| translates back to Agda world
        \item Note building of environment and final interpretation
    \end{itemize}

\begin{code}
prependTelescope   : (n m : ℕ) → Diff n m → BoolExpr m → Env n → Set
prependTelescope   .m m    (Base    ) b env = P ⟦ env ⊢ b ⟧
prependTelescope    n m    (Step y  ) b env =
  (a : Bool) → prependTelescope (suc n) m y b (a ∷ env)

forallBool : (m : ℕ) → BoolExpr m → Set
forallBool m b = prependTelescope zero m (zero-least 0 m) b []
\end{code}
\end{frame}
}



\ignore{
\begin{code}
-- dependently typed if-statement
if : {P : Bool → Set} → (b : Bool) → P true → P false → P b
if true  t f = t
if false t f = f

-- very much like ⊥-elim, but for Errors.
Error-elim : ∀ {Whatever : Set} {e : String} → Error e → Whatever
Error-elim ()
\end{code}
} % endignore


\ignore{
\begin{frame}
    \begin{itemize}
        \item Finally we can consolidate things about the decision function
        \item This represents a tree with decisions in the leaves
        \item Each leaf represents a different environment (left = |true|, right  = |false|)
        \item Remember, |P| evaluates to |⊥| if the expression holds
        \item The entire object |foralls expression| represents the proof obligation for a tautology
        \item i.e. with this fact, we can show some $b$ is a tautology
    \end{itemize}
\begin{code}
forallsAcc : {n m : ℕ} → (b : BoolExpr m) → Env n → Diff n m → Set
forallsAcc b' env    (Base     ) = P ⟦ env ⊢ b' ⟧
forallsAcc b' env    (Step y   ) =
  forallsAcc b' (true ∷ env) y × forallsAcc b' (false ∷ env) y

foralls : {n : ℕ} → (b : BoolExpr n) → Set
foralls {n} b = forallsAcc b [] (zero-least 0 n)
\end{code}
\end{frame}

} % endignore

\ignore{
\begin{frame}
    \begin{itemize}
        \item Given this fact, we can find the right proof for any given environment
        \item \ldots thus proving a given formula is a tautology.
        \item Note: |foralls b| is an implicit argument
    \end{itemize}
\begin{code}
soundnessAcc :   {m : ℕ} → (b : BoolExpr m) →
     {n : ℕ} → (env : Env n) →
     (d : Diff n m) → forallsAcc b env d →
     prependTelescope n m d b env
soundnessAcc     bexp     env Base     H with ⟦ env ⊢ bexp ⟧
soundnessAcc     bexp     env Base     H | true  = H
soundnessAcc     bexp     env Base     H | false = Error-elim H
soundnessAcc {m} bexp {n} env (Step y) H =
    λ a → if {λ b → prependTelescope (suc n) m y bexp (b ∷ env)} a
        (soundnessAcc bexp (true  ∷ env) y (proj₁ H))
        (soundnessAcc bexp (false ∷ env) y (proj₂ H))

soundness : {n : ℕ} → (b : BoolExpr n) → {i : foralls b} → forallBool n b
soundness {n} b {i} = soundnessAcc b [] (zero-least 0 n) i
\end{code}
\end{frame}


}   % end ignore

\begin{frame}
    \begin{itemize}
        \item Next, skipped: proving soundness of interpretation function
        \item Now we can prove tautologies using just |soundness b| with $b$ an expression
        \item Still not ideal though, we need to represent the formula manually\ldots
\begin{code}
rep          : BoolExpr 2

someTauto    :      (p q : Bool)
             →      P ( p ∧ q ⇒ q )
rep          = Imp  (And    (Atomic (suc zero))
                            (Atomic zero))
                    (Atomic zero)

someTauto    = soundness rep
\end{code}
            \vskip -10mm
            \pause
        \item Cluttered, error-prone
        \item Reflection API to the rescue!
    \end{itemize}
\end{frame}


\section{Adding Reflection}\label{sec:addrefl}


\begin{frame}{Adding Reflection (in the programming language sense)}
    \begin{itemize}
        \item Agda now includes the |quoteGoal| keyword\cite{agda-relnotes-228}
        \item Produces an expression of type |Term|
        \item We can convert this to our |BoolExpr| type, using a few helpers
        %\item Note all the implicit arguments
    \end{itemize}
\end{frame}

\ignore{
\begin{frame}
\scriptsize{
\begin{code}
concrete2abstract :
             (t     : Term)
       →     {pf    : isSoExprQ (stripPi t)}
       →     {pf2   : isBoolExprQ (freeVars t) (stripPi t) pf}
       →     BoolExpr (freeVars t)
concrete2abstract t {pf} {pf2} = term2boolexpr  (freeVars t)
                                                (stripSo (stripPi t) pf)
                                                pf2

proveTautology :    (t     : Term) →
                    {pf    : isSoExprQ (stripPi t)} →
                    {pf2   : isBoolExprQ (freeVars t) (stripPi t) pf} →
                    let b = concrete2abstract t {pf} {pf2} in
                        {i : foralls b} →
                        forallBool (freeVars t) b
proveTautology e {pf} {pf2} {i} = soundness     {freeVars e}
                                                (concrete2abstract e) {i}

\end{code}
}
\end{frame}

} % end ignore

\begin{frame}
    \begin{itemize}
        \item This allows generating proofs as follows
    \end{itemize}
\begin{code}
exclMid    : (b : Bool) → P (b ∨ ¬ b)
exclMid    = quoteGoal e in proveTautology e

peirce     : (p q : Bool) → P (((p ⇒ q) ⇒ p) ⇒ p)
peirce     = quoteGoal e in proveTautology e

mft        : t1
mft        = quoteGoal e in proveTautology e
\end{code}
\end{frame}

\subsection{Summarising proof by reflection}

\begin{frame}
    In summary:
    \begin{itemize}
        \item Define abstract representation of proposition
        \item Decide if a particular instance holds
        \item Show soundness of decision
        \item ``Reflect'' abstract representation back to concrete proposition
    \end{itemize}
    Our contribution in this process:
    \begin{itemize}
        \item Automatically generate abstract representation
        \item Saves tedium, frustration and redundancy
    \end{itemize}
\end{frame}


\section{Further Work}

\begin{frame}
    Some ideas for using reflection:
    \begin{itemize}
        \item Well-typed lambda term rewriting % : eg. into SKI or CPS (continuation passing style)
        \begin{itemize}
            \item Nice illustration of DTP and reflection (one can express constraints in datatype of lambda terms)
        \end{itemize}
        \item Generating embedding-projection pairs for generic programming, given some datatype definition
        \begin{itemize}
            \item Will need a little embellishment to the compiler
        \end{itemize}
    \end{itemize}
\end{frame}


\section{Related Work}

\begin{frame}
    \begin{itemize}
        \item Adam Chlipala's proof-by-reflection tutorial for Coq\cite{chlipala2011certified}
        \item Wojciech Jedynak's ring solver in Agda\cite{ringsolver}
    \end{itemize}
\end{frame}



\bibliography{refs}{}
\bibliographystyle{splncs}



\end{document}
