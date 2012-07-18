\documentclass[a4paper]{llncs}

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


\begin{spec}
-- imports for Evenness
open import Relation.Binary.PropositionalEquality
open import Data.Bool renaming (not to ¬_)
open import Data.Nat
\end{spec}
}

\ignore{
\begin{spec}
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
\end{spec}
}

\usepackage{amsmath}
\usepackage{semantic}
% things for the semantic package
\reservestyle{\command}{\textbf}
\command{let,in,:,case,of,if,then,else,letrec,nil,cons,false,true,[]}
\mathlig{ -->}{\longrightarrow}



\author{Paul van der Walt \and Wouter Swierstra}
\date{\today}
\title{Proof by reflection by reflection}
\institute{
\email{W.S.Swierstra@@uu.nl}, \email{paul@@denknerd.org}\\
Department of Computer Science, Utrecht University
}

\begin{document}

\maketitle


\begin{abstract}
Hi, this is an abstract.
\end{abstract}


\input{introduction.tex}

\section{Proof by Reflection}\label{sec:proof-by-reflection}


The idea behind proof by reflection is that one needn't produce a large proof tree
for each proof instance one wants to have, but rather proves the soundness of
a decision function, in effect giving a ``proof recipe'' which can be instantiated
when necessary.

One has to translate the problem into an abstract (equivalent) representation, invoke
the soundness of the decision function which was defined (assuming it returns |true| for
the AST instance), giving the proof of the given proposition.

Reflection is an overloaded word in this context, since in programming language technology
reflection is the capability of converting some piece of concrete program syntax into a syntax tree
object which can be manipulated in the same system. These values (in terms of inductive types representing
the concrete syntax) can then be translated back into concrete terms, a process which is called reflection.


Here we will present two case studies illustrating proof by reflection and how reflection
(in the programming language sense) can make the technique more usable and accessible.






\subsection{Simple Example: Evenness}

Take as an example the property of evenness on natural numbers. One has two
rules, namely the rule that says that zero is even, and the
rule that says that if $n$ is even, then $n+2$ is also even.


\begin{center}
\begin{tabular}{ccc}
\inference[zero-even]{}{|Even 0|}\label{evenzero} & ~~~ & \inference[ss-even]{|Even n|}{|Even (suc (suc n))|}\label{evenzero}
\end{tabular}
\end{center}


When translated into an Agda data type, the property of evenness can be naturally expressed
as follows.


\begin{spec}
data Even      : ℕ → Set where
  isEvenZ      :                          Even 0
  isEvenSS     : {n : ℕ} → Even n     →   Even (2 + n)
\end{spec}

If one has to use these rules to produce the proof tree each time a
proof of evenness is required for some $N$, this would be tedious.
One would need to unfold the number using |isEvenSS| half the size
of the number. For example, to prove that 6 is even, one would require
the following proof.

\begin{spec}
isEven6 : Even 6
isEven6 = isEvenSS (isEvenSS (isEvenSS isEvenZ))
\end{spec}

Obviously, this proof tree grows as the natural for which one would
like to show evenness for becomes larger.

A solution here is to use proof by reflection. The basic technique is as follows.
Define a decision function, called |even?| here, which produces some binary
value (in our case a |Bool|) depending on if the input is even or not.
This function is rather simple in our case.

\begin{spec}
even? : ℕ → Bool
even? zero              = true
even? (suc zero)        = false
even? (suc (suc n))     = even? n
\end{spec}

Now one can ask whether some value is even or not. Next we need to show that
our decision function actually tells the truth. We need to prove that
|even?| returns |true| iff a proof |Even n| can be produced. This is done in
the function |soundnessEven|. What is actually happening here is that we are
giving a recipe for proof trees such as the one we manually defined for |isEven6|.

\begin{spec}
soundnessEven : {n : ℕ} → even? n ≡ true → Even n
soundnessEven {0}              refl        = isEvenZ
soundnessEven {1}              ()
soundnessEven {suc (suc n)}    s           = isEvenSS (soundnessEven s)
\end{spec}

Now that this has been done, if we need a proof that some arbitrary $n$ is even,
we only need to instantiate |soundnessEven|. Note that the value of $n$ is a hidden
and automatically inferred argument to |soundnessEven|, and that we also pass
a proof that |even? n| returns |true| for that particular $n$. Since in a
dependently typed setting $\beta$-reduction (evaluation) happens in
the type system, |refl| is a valid proof.

\begin{spec}
isEven28        : Even 28
isEven28        = soundnessEven refl

isEven8772      : Even 8772
isEven8772      = soundnessEven refl
\end{spec}

Now we can easily get a proof that arbitrarily large numbers are even,
without having to explicitly write down a large proof tree. Note that
it's not possible to write something with type |Even 27|, or any other uneven
number, since the parameter |even? n ≡ true| cannot be instantiated, thus
|refl| won't be accepted where it is in the |Even 28| example. This will
produce a |true !≡ false| type error at compile-time.



\subsection{Second Example: Boolean Tautologies}

Another example of an application of the proof by reflection technique is
boolean expressions which are a tautology. We will follow the same recipe
as for even naturals.

Take as an example the boolean formula in equation \ref{eqn:tauto-example}.

\begin{align}\label{eqn:tauto-example}
(p_1 \vee q_1) \wedge (p_2 \vee q_2) \Rightarrow (q_1 \vee p_1) \wedge (q_2 \vee p_2)
\end{align}

It is trivial to see that this is a tautology, but proving this fact using basic
equivalence rules for booleans would be rather tedious. It's even worse if we want
to check if the formula always holds by trying all possible variable assignments,
since this will give $2^n$ cases, where $n$ is the number of variables.

To try to automate this process, we'll follow a similar approach to the one given
above for proving evenness of arbitrary (even) naturals.

We start off by defining an inductive data type to represent
boolean expressions with $n$ free variables,
using de Bruijn indices.  There isn't anything surprising about this
definition; we use the type |Fin n| to ensure that variables
(represented by |Atomic|) are always in scope.

Our language supports boolean and, or, not, implication and arbitrary unknown
boolean formulae represented by the constructor |Atomic|. The natural number in
|Atomic| contains the de Bruijn index of a variable in the environment.

\begin{spec}
data BoolExpr : ℕ → Set where
  Truth         : {n : ℕ}                                → BoolExpr n
  Falsehood     : {n : ℕ}                                → BoolExpr n
  And           : {n : ℕ} → BoolExpr n → BoolExpr n      → BoolExpr n
  Or            : {n : ℕ} → BoolExpr n → BoolExpr n      → BoolExpr n
  Not           : {n : ℕ} → BoolExpr n                   → BoolExpr n
  Imp           : {n : ℕ} → BoolExpr n → BoolExpr n      → BoolExpr n
  Atomic        : {n : ℕ} → Fin n                        → BoolExpr n
\end{spec}

We also need a mapping from variables to boolean assignments, which we'll call |Env|.
It has fixed size $n$ since a |BoolExpr n| has $n$ free variables.

\begin{spec}
Env   : ℕ → Set
Env   = Vec Bool
\end{spec}

Now we can define our decision function, which decides if a given
boolean expression is a tautology. It does this by evaluating (interpreting)
the formula's AST. For example, |And| is converted to the boolean function |_∧_|,
and it's two arguments in turn are recursively interpreted. Here |_∧_|, |_∨_|, |_⇒_| are
all defined with type |Bool → Bool → Bool|, and |¬_| is of type |Bool → Bool|.
The interpretation function |⟦_⊢_⟧| is unsurprising.

\ignore{
\begin{spec}
infixr 4 _⇒_
_⇒_ : Bool → Bool → Bool
true  ⇒ true  = true
true  ⇒ false = false
false ⇒ true  = true
false ⇒ false = true
\end{spec}
}




\begin{spec}
⟦_⊢_⟧ : ∀ {n : ℕ} (e : Env n) → BoolExpr n → Bool
⟦ env     ⊢ Truth       ⟧ = true
⟦ env     ⊢ Falsehood   ⟧ = false
⟦ env     ⊢ And be be₁  ⟧ =     ⟦ env ⊢ be ⟧     ∧      ⟦ env ⊢ be₁ ⟧
⟦ env     ⊢ Or be be₁   ⟧ =     ⟦ env ⊢ be ⟧     ∨      ⟦ env ⊢ be₁ ⟧
⟦ env     ⊢ Not be      ⟧ = ¬   ⟦ env ⊢ be ⟧
⟦ env     ⊢ Imp be be₁  ⟧ =     ⟦ env ⊢ be ⟧     ⇒      ⟦ env ⊢ be₁ ⟧
⟦ env     ⊢ Atomic n    ⟧ = lookup n env
\end{spec}


Note that the interpretation function also requires an environment to be
provided, which maps the free variables to actual boolean values. The type of
the interpretation function ensures that the mapping always contains an entry
for each free variable.

Now that this has been done, we can move on to defining what it means for a given
formula to be a tautology. Here we introduce the |So| function, which gives |⊤| if
its argument is |true|, and |⊥| otherwise. We've actually defined a type isomorphic to |⊥|
which is parameterised by an error message string, to make it more obvious to the user
what went wrong, if anything.





\begin{spec}
data Error (a : String) : Set where

So : String → Bool → Set
So _ true  = ⊤
So s false = Error s

P : Bool → Set
P = So "Expression doesn't evaluate to true in this branch."
\end{spec}

Now that we have these helper functions, it's easy to express a tautology. We quantify over
a few boolean variables, and wrap the formula in our |P| function. If this function can be defined,
we have proven that the argument to |P| is a tautology, i.e. for each assignment of the free variables
the entire equation still evaluates to |true|.

\begin{spec}
b⇒b : (b : Bool) → P(b ⇒ b)
b⇒b true  = tt
b⇒b false = tt
\end{spec}

This seems fine, but as soon as more variables come into play, the proofs we need to construct become
rather tedious. Take the following formula as an example; it would need 16 cases. Note that this is
the same formula as in Eqn. \ref{eqn:tauto-example}.

\begin{spec}
myfavouritetheorem : Set
myfavouritetheorem = (p1 q1 p2 q2 : Bool)   →   P  (      (p1 ∨ q1) ∧ (p2 ∨ q2)
                                                      ⇒   (q1 ∨ p1) ∧ (q2 ∨ p2)
                                                   )
\end{spec}

What we would actually like to do, however, is prove the soundness of our decision function |⟦_⊢_⟧|, which would
do away with the need to manually construct each proof. First we need to give a relation between a term
of type |BoolExpr n| and |Set|, since theorems in Agda have type |Set|. 



\ignore{
\begin{spec}
data Diff : ℕ → ℕ → Set where
  Base : ∀ {n}   → Diff n n
  Step : ∀ {n m} → Diff (suc n) m → Diff n m
\end{spec}

\begin{spec}
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

\end{spec}
}

The function |forallBool| turns a |BoolExpr n| back into something Agda recognises as a theorem.
First it prepends $n$ binding sites for boolean variables (representing the free variables in the
formula), after which it calls the decision function, passing the new free variables as the environment.


\begin{spec}
prependTelescope   : (n m : ℕ) → Diff n m → BoolExpr m → Env n → Set
prependTelescope   .m m    (Base    ) b env = P ⟦ env ⊢ b ⟧ 
prependTelescope    n m    (Step y  ) b env =
  (a : Bool) → prependTelescope (suc n) m y b (a ∷ env)
  

forallBool : (m : ℕ) → BoolExpr m → Set
forallBool m b = prependTelescope zero m (zero-least 0 m) b []
\end{spec}

\ignore{
\begin{spec}
-- dependently typed if-statement
if : {P : Bool → Set} → (b : Bool) → P true → P false → P b
if true  t f = t
if false t f = f

-- very much like ⊥-elim, but for Errors.
Error-elim : ∀ {Whatever : Set} {e : String} → Error e → Whatever
Error-elim ()
\end{spec}
}

Now that we can translate a |BoolExpr n| into a concrete Agda theorem, and we have a way to decide if something
is true for a given environment, we need to show the soundness of our decision function, and define a notion
of what it means to be a tautology. That is, we need to be able to show that a formula is true for every
possible assignment of its variables to |true| or |false|.

The first step in this process is to formalise the idea of a formula being true for all variable assignments.
This is captured in the functions |foralls| and |forallsAcc|, where |foralls| is the function which bootstraps
the construction of a tree, where the leaves represent the truth of a proposition given a certain assignment
of variables. Each time there's a branch in the (fully binary) tree, the left branch at depth $d$ corresponds to
setting variable with de Bruijn index $d$ to |true|, and the right branch corresponds to setting that variable
to |false|. |Diff n m| is an auxiliary proof that the process terminates, and that in the end the environments
will all have $n$ entries, corresponding to the $n$ free variables in a |BoolExpr n|.

\begin{spec}
forallsAcc : {n m : ℕ} → (b : BoolExpr m) → Env n → Diff n m → Set
forallsAcc b' env    (Base     ) = P ⟦ env ⊢ b' ⟧
forallsAcc b' env    (Step y   ) =
  forallsAcc b' (true ∷ env) y × forallsAcc b' (false ∷ env) y

foralls : {n : ℕ} → (b : BoolExpr n) → Set
foralls {n} b = forallsAcc b [] (zero-least 0 n)
\end{spec}

We now have a concept of all environments leading to truth of a proposition. If we require this
fact as input to a soundness function, we are able to use it to show that the current boolean
expression is in fact a tautology. We do this in the |soundness| function, where the output should
have the type given by the previously-defined |prependTelescope| function. This enables us to put a
call to |soundness| where a proof of something like Eqn. \ref{eqn:tauto-example} is required.

If we look closely at the definition of |soundnessAcc| (which is actually where the work is done; |soundness|
merely calls |soundnessAcc| with some initial input, namely the |BoolExpr n|, an empty environment, and
the proof that the environment is the size of the number of free variables), we see that we build up a
function that, when called with the values assigned to the free variables, builds up the corresponding
environment and eventually returns the leaf from |foralls| which is the proof that the formula
is a tautology in that specific case.

\begin{spec}
soundnessAcc :   {m : ℕ} →
                 (b : BoolExpr m) →
                 {n : ℕ} →
                 (env : Env n) →
                 (d : Diff n m) →
                 forallsAcc b env d →
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
\end{spec}

Notice that |foralls b| is an implicit argument to |soundness|, which might be surprising, since
it is actually the proof tree representing that the expression is a tautology. The reason this is how it's
done is because Agda can automatically infer implicit arguments when they are simple record types, such as
|⊤| and pair in this case. This is illustrated in the following code snippet.

\begin{spec}
foo : {u : ⊤ × ⊤} → ℕ
foo = 5

baz : ℕ
baz = foo
\end{spec}

Here we see that there is an implicit argument |u| required to |foo|, but in |baz| it's not given.
This is possible because Agda can infer that |(tt , tt)| is the only term which fits, and therefore
instantiates it when required. This can be done by the type system for records, since they are not allowed
to be inductively defined, which would cause possible non-termination.

The same principle is used in |soundness|; eventually all that's required
is a deeply nested pair containing elements of type |⊤|, of which |tt| is the only constructor. If the
formula isn't a tautology, there's no way to instantiate the proof, since it will have type |⊥|, as a
result of the use of |So|. In other words, the fact that the proof tree can be constructed corresponds exactly
to those cases when the expression is a tautology. Therefore, we needn't instantiate |soundness| with a
manually-crafted tree of |⊤|s, we can just let Agda do the work.

Now, we can prove theorems by calling |soundness b|, where |b| is the representation of the formula
under consideration. Agda is convinced that the representation does in fact correspond to the concrete formula,
and also that |soundness| gives a valid proof. If the module passes the type-check, we know our formula
is both a tautology, and that we have the corresponding proof object at our disposal afterwards,
as in the following example.


\begin{spec}
rep          : BoolExpr 2

someTauto    : (p q : Bool)
             → P( p ∧ q ⇒ q )
rep          = Imp (And (Atomic (suc zero)) (Atomic zero)) (Atomic zero)

someTauto    = soundness rep
\end{spec}

The only thing which is still a pain is that for every formula we'd like a tautology-proof of,
we have to manually convert the concrete Agda representation (|p ∧ q ⇒ q|, in this case) into our
abstract syntax
(|rep| here). This is silly,
since we end up typing out the formula twice. We also have to count the number of free variables ourselves,
and keep track of the de Bruijn indices. This is error-prone given how cluttered the abstract representation
can get for formulae containing many
variables. It would be desirable for this process to be automated. In Sec. \ref{sec:addrefl} an approach is
presented using Agda's recent reflection API.

\subsection{Adding Reflection}\label{sec:addrefl}

In Agda version 2.2.8 a reflection API was added \cite{agda-relnotes-228}. This system introduces some extra
language constructs, such as |quoteGoal e in t|, which allows the term |t| to refer to |e|, which is instantiated
to an abstract representation of the type of the term expected wherever |quoteGoal| was placed. Since
one needs to encode the desired proposition to be proved in the type of the proof object, quoting
this goal gives us enough information to call the |soundness| function. Here we see 2 helper functions
for doing precisely that.

|proveTautology| calls the |soundness| function, after converting the raw AST (abstract syntax tree)
Agda gives us representing the goal into our own |BoolExpr n| format. To be able to do this is also
needs some auxiliary functions such as |freeVars|, which counts the number of variables (needed to
be able to instantiate the $n$ in |BoolExpr n|), and |stripSo| \& |stripPi|, which peel off the telescope
type and the function |P| with which we wrap our tautologies. We also need the |concrete2abstract| function,
which does the actual |Term → BoolExpr n| conversion, when given proofs that the input |Term| adheres to
certain restrictions (such as only containing the functions |_∧_|, |_∨_| and friends, and only containing
boolean variables.

The helper functions have been ommitted for brevity, since they are rather verbose and don't add anything
to the understanding of the subject at hand.

\begin{spec}
concrete2abstract :
             (t     : Term)
       →     {pf    : isSoExprQ (stripPi t)}
       →     {pf2   : isBoolExprQ (freeVars t) (stripPi t) pf}
       →     BoolExpr (freeVars t)
concrete2abstract t {pf} {pf2} = term2boolexpr (freeVars t) (stripSo (stripPi t) pf) pf2

proveTautology :    (t     : Term) →
                    {pf    : isSoExprQ (stripPi t)} →
                    {pf2   : isBoolExprQ (freeVars t) (stripPi t) pf} →
                    let b = concrete2abstract t {pf} {pf2} in
                        {i : foralls b} →
                        forallBool (freeVars t) b
proveTautology e {pf} {pf2} {i} = soundness {freeVars e} (concrete2abstract e) {i}

\end{spec}

These are all the ingredients required to automatically prove that formulae are tautologies.
The following code illustrates the use of the |proveTautology| functions; we can omit the implicit
arguments for the reasons outlined in the previous section.

\begin{spec}

exclMid    : (b : Bool) → P(b ∨ ¬ b)
exclMid    = quoteGoal e in proveTautology e

peirce     : (p q : Bool) → P(((p ⇒ q) ⇒ p) ⇒ p)
peirce     = quoteGoal e in proveTautology e

mft        : myfavouritetheorem
mft        = quoteGoal e in proveTautology e
\end{spec}


This shows that the reflection capabilities recently added to Agda are certainly useful for
automating certain tedious tasks, since the programmer now needn't encode the boolean expression
twice in a slightly different format, but just lets the conversion happen automatically, without loss
of expressive power or general applicability of the proofs resulting from |soundness|.





\section{Type-safe metaprogramming}\label{sec:type-safe-metaprogramming}




\section{Documenting the Reflection API}\label{sec:refl-docu}





\section{Related Work}

Mention AChlipala and wjzz here.


\section{Further Work}

We should continue.

\section{Conclusion}


Lorem ipsum dolor sit amet.

\bibliography{refs}{}
\bibliographystyle{splncs}



\end{document}
