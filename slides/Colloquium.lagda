\documentclass[usenames,svgnames,dvipsnames,table]{beamer}
%include polycode.fmt
%include agda.fmt
%include generated-colour.fmt
%include codecolour.fmt

\renewcommand{\textbeta}{\ensuremath{\beta}}


\usepackage{tgpagella}
\usepackage[T1]{fontenc}

\usetheme{Berlin}
\newcommand{\ppause}{\pause \vspace{ -2em}}
\newcommand{\ignore}[1]{}

\ignore{
\begin{code}
module slides.Colloquium where
\end{code}
}
\ignore{
\begin{code}

open import Data.Sum
open import Data.Product
open import Reflection
open import Metaprogramming.Autoquote renaming (_#_↦_ to _\#_↦_)

\end{code}
}

\title{Reflection in Agda}
\author{Paul van der Walt}
\institute[Dept. of CS @@ UU.nl]{Supervisors: Wouter Swierstra and Johan Jeuring\\ Department of Computing Science, Utrecht University}
\date{4$^{\text{th}}$ of October, 2012}

\begin{document}


\begin{frame}
\maketitle
\end{frame}

\setcounter{tocdepth}{1}
\begin{frame}
  \tableofcontents
\end{frame}

\section{Introduction}



\begin{frame}
  \frametitle{Introduction}
  \begin{itemize}
  \item Agda: dependently typed functional programming language
  \item Functions must be \emph{total}
  \end{itemize}
\end{frame}


\subsection{Definitions}

\ignore{
  \begin{code}
open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Fin hiding (_+_)
open import Data.Vec hiding (_∈_)
open import Data.List
open import Data.Bool renaming (not to ¬_)
open import Proofs.Util.Handy
open import Proofs.Util.Types
  \end{code}
  }


\begin{frame}
  \frametitle{Naturals}
  \begin{itemize}
  \item Definition of naturals in Agda
  \end{itemize}
  \begin{spec}
data ℕ : Set where
  zero     :          ℕ
  suc      : ℕ ->     ℕ
  \end{spec}
  
\end{frame}
\begin{frame}
  \frametitle{Evenness}
  \begin{itemize}
  \item Evenness rules
  \end{itemize}
  \begin{code}
data Even      : ℕ → Set where
  isEven0      :                          Even 0
  isEven+2     : {n : ℕ} → Even n     →   Even (2 + n)
  \end{code}
  
\end{frame}




\begin{frame}
  \frametitle{A Proof}
\begin{code}
isEven10 : Even 10
isEven10 =      isEven+2
                   (isEven+2
                     (isEven+2
                       (isEven+2
                         (isEven+2
                           isEven0))))
\end{code}
  \begin{itemize}
  \item Rather cumbersome!
  \item Solution: proof by reflection
  \end{itemize}

\end{frame}


\begin{frame}
  \frametitle{Proof by Reflection}
  \begin{itemize}
  \item \emph{Build} proof by inspecting terms
  \item Here: what is $n \rightarrow$  build proof
  \item Basic idea:
    \begin{enumerate}
    \item Decision procedure
    \item Soundness of decision procedure
    \item Generate proof for each instance
    \end{enumerate}
  \end{itemize}
  
\end{frame}

\section{Proof by Reflection}

\subsection{Evenness example}



\begin{frame}
  \frametitle{Evenness decision}
  \begin{itemize}
  \item Step 1: decision procedure
  \item Intermezzo: Curry--Howard isomorphism (whiteboard)
  \end{itemize}
\begin{code}
even? : ℕ → Set
even? 0                 = ⊤
even? 1                 = ⊥
even? (suc (suc n))     = even? n
\end{code}
\end{frame}

\begin{frame}
  \frametitle{Soundness}
  \begin{itemize}
  \item Step 2: soundness of decision
  \item Remember C--H says: proven once implemented
  \item Thus, soundness \emph{builds} the proof tree, iff it exists
  \end{itemize}
\begin{code}
soundnessEven : (n : ℕ) → even? n → Even n
soundnessEven 0              tt        = isEven0
soundnessEven 1              ()
soundnessEven (suc (suc n))  s         = isEven+2 (soundnessEven n s)
\end{code}
\end{frame}

\begin{frame}
  \frametitle{Usage}
  \begin{itemize}
  \item Step 3: apply definition of soundness
  \item Step 4: profit!
  \end{itemize}
\begin{code}
isEven28        : Even 28
isEven28        = soundnessEven 28       tt

isEven8772      : Even 8772
isEven8772      = soundnessEven 8772     tt
\end{code}
\end{frame}





\ignore{
\begin{code}
open import Proofs.Util.Lemmas
open import Proofs.TautologyProver renaming (soundness to soundnessImplicit)

soundness       : {n : ℕ} → (b : BoolExpr n) → foralls b
                → proofGoal n b
soundness  b p  = soundnessImplicit b {p}
\end{code}
}

\subsection{Booleans example}

\begin{frame}
  \frametitle{Boolean tautologies}
  \begin{itemize}
  \item Many possible applications of proof by reflection
  \item Another example: prove that a formula is a tautology
  \item E.g. $p ∨ ¬ p$; always true
  \end{itemize}
\end{frame}

\begin{frame}
  \frametitle{Introducing BoolExpr}
  \begin{itemize}
  \item Boolean formulae with max. $n$ free variables
  \end{itemize}
\begin{spec}
data BoolExpr (n : ℕ) : Set where
  Truth         :                                  BoolExpr n
  Falsehood     :                                  BoolExpr n
  And           : BoolExpr n → BoolExpr n      →   BoolExpr n
  Or            : BoolExpr n → BoolExpr n      →   BoolExpr n
  Not           : BoolExpr n                   →   BoolExpr n
  Imp           : BoolExpr n → BoolExpr n      →   BoolExpr n
  Atomic        : Fin n                        →   BoolExpr n
\end{spec}
\end{frame}

\ignore{
\begin{spec}
Env   : ℕ → Set
Env   = Vec Bool
\end{spec}
}

\begin{frame}
  \frametitle{Decision}
  \begin{itemize}
  \item Decision is evaluation
  \item But, map |true| to |⊤| and |false| to |⊥| (Agda propositions)
  \end{itemize}
\begin{spec}
⟦_⊢_⟧ : ∀ {n : ℕ} (e : Env n) → BoolExpr n → Bool
⟦ env     ⊢ Truth           ⟧ = true
⟦ env     ⊢ Falsehood       ⟧ = false
⟦ env     ⊢ And   be   be₁  ⟧ =     ⟦ env ⊢ be ⟧     ∧      ⟦ env ⊢ be₁ ⟧
⟦ env     ⊢ Or    be   be₁  ⟧ =     ⟦ env ⊢ be ⟧     ∨      ⟦ env ⊢ be₁ ⟧
⟦ env     ⊢ Not   be        ⟧ = ¬   ⟦ env ⊢ be ⟧
⟦ env     ⊢ Imp   be   be₁  ⟧ =     ⟦ env ⊢ be ⟧     ⇒      ⟦ env ⊢ be₁ ⟧
⟦ env     ⊢ Atomic n        ⟧ = lookup n env
\end{spec}
\end{frame}

\begin{frame}
  \frametitle{Problem statement}
  \begin{itemize}
  \item What do we want to prove?
  \end{itemize}
\begin{spec}
someTauto    : (p q : Bool)         → P( p ∧ q ⇒ q )
someTauto    = (HOLE 0)
\end{spec}
\end{frame}

\begin{frame}
  \frametitle{Proving soundness}
  \begin{itemize}
  \item How will we prove soundness?
  \item Turns out to be involved.
  \end{itemize}
\begin{spec}
soundness       : {n : ℕ} → (b : BoolExpr n) → foralls b
                → proofGoal n b
\end{spec}
Here, |proofGoal n b| returns a type with $n$ fresh Booleans, like

\begin{spec}
(p q r : Bool) → P b
\end{spec}
\end{frame}

\begin{frame}
  \frametitle{Usage}
  \begin{itemize}
  \item Assuming we have |soundness|, we can easily prove tautologies.
  \end{itemize}
\begin{code}
rep          : BoolExpr 2
rep          = Imp    (And (Atomic (suc zero)) (Atomic zero)) 
                      (Atomic zero)

someTauto    : (p q : Bool)         → P( (p ∧ q) ⇒ q )
someTauto    = soundness rep _
\end{code}
\pause
\begin{itemize}
\item But, oh no! The duplication!
\end{itemize}
\end{frame}

\subsection{Enter reflection!}

\begin{frame}
  \frametitle{Reflecting in Agda}
  \begin{itemize}
  \item The API lets us do |quote|, |unquote| or |quoteGoal|
  \end{itemize}
\begin{spec}
someTauto2   : (p : Bool)         → P (p ∨ ¬ p)
someTauto2   = quoteGoal e in (HOLE 0)
\end{spec}
\pause
\begin{spec}
e :   Term
e ≡   pi    (... Bool...) -- intro variable p
            (def So (arg (def _∨_ (   arg (var 0 []) ∷
                                      arg (def ¬_  (arg     (var 0 [])
                                      ∷ [])) ∷ [])) ∷ []))
\end{spec}
\end{frame}

\begin{frame}
  \begin{itemize}
  \item How can we distil a |BoolExpr| from a |Term|?
  \item Enter |Autoquote|!
  \item Provide a mapping: 
  \end{itemize}
\begin{code}
boolTbl : Table BoolIntermediate
boolTbl =   (Atomic ,
                  2 \# (quote _∧_      ) ↦ And
            ∷     2 \# (quote _∨_      ) ↦ Or
            ∷     1 \# (quote  ¬_      ) ↦ Not
            ∷     0 \# (quote true     ) ↦ Truth
            ∷     0 \# (quote false    ) ↦ Falsehood
            ∷     2 \# (quote _⇒_      ) ↦ Imp ∷ [])
\end{code}
\end{frame}

\begin{frame}
  \begin{itemize}
  \item We now use the |doConvert| function
  \end{itemize}
\begin{code}
term2bool_auto     : (t : Term)
                   → {pf : convertManages boolTbl t}
                   → BoolIntermediate
term2bool_auto t {pf} = doConvert boolTbl t {pf}
\end{code}
  
\end{frame}

\begin{frame}
  \frametitle{Assembling the pieces}
  \begin{itemize}
  \item We can now automatically quote to |BoolExpr|, 
  \item then get a proof using |soundness|.

  \item Automatic proof generation.
  \end{itemize}
\begin{code}
someTauto2   : (p : Bool)         → P (p ∨ ¬ p)
someTauto2   = quoteGoal e in proveTautology e
\end{code}
\end{frame}

\begin{frame}
  \frametitle{Interim Summary}
  Contributions:
  \begin{itemize}
  \item Automatic quoting to simple AST @Autoquote@
  \item Illustration of proof by reflection
  \item Guide to using Agda's reflection API (example code + chapter in thesis)
  \end{itemize}
\end{frame}




\ignore{
\begin{code}
open import Relation.Binary.PropositionalEquality
open import Metaprogramming.ExampleUniverse
open DT hiding (Well-typed-closed) renaming (U' to Uu) 
open import Metaprogramming.Util.Equal
open TC
open SKI'
\end{code}}




\section{Metaprogramming}



\begin{frame}
  \frametitle{Definitions}

  \begin{quotation}
Metaprogramming is the writing of computer programs that write or manipulate other programs (or themselves) as their data\ldots
  \end{quotation}
  \begin{quotation}
Reflection is when a programming language (object language) can be its own metalanguage.
  \end{quotation}
\end{frame}


\begin{frame}
  \frametitle{Powerful type system}
  \begin{itemize}
  \item Reflection has existed for a long time
  \item Used extensively in Lisp
  \item What advantage does Agda offer?
  \item \emph{Dependent types}
  \end{itemize}
\end{frame}

\subsection{Metaprogramming framework}

\begin{frame}
  \begin{itemize}
  \item Our object language: simply typed lambda calculus
  \item Application, abstraction, variables
  \item De Bruijn representation
  \end{itemize}
\end{frame}


\begin{frame}
  \frametitle{Refreshing our memory}
  \begin{itemize}
  \item What is the De Bruijn representation?
  \item Nameless variables
  \item Identified by number of abstractions ($\lambda$s) between call and binding site
  \end{itemize}
  \begin{center}
    \begin{tabular}{c||c}
      Named & De Bruijn \\
      \hline
      $\lambda x . x$ & $\lambda . 0$\\
      $\lambda x . \lambda y . x y$ & $\lambda . \lambda . 1~0$\\
    \end{tabular}
  \end{center}
\end{frame}

  


\subsection{Definitions}


\begin{frame}
  \begin{itemize}
  \item Recall the STLC typing rules; rather a literal translation here.
  \item Using |WT| we can do type-preserving transformations
  \end{itemize}
\begin{code}
data WT' : Ctx →                     Uu → Set where
  Var   : ∀ {Γ} {τ}
                   → τ ∈ Γ
                   → WT' Γ           τ              
  Lam   : ∀ {Γ} σ {τ}
                   → WT' (σ ∷ Γ)     τ             
                   → WT' Γ           (σ => τ)     
  _⟨_⟩  : ∀ {Γ} {σ τ}
                   → WT' Γ           (σ => τ)    
                   → WT' Γ           σ          
                   → WT' Γ           τ         

Well-typed-closed = WT []
\end{code}
\end{frame}

\begin{frame}
  \frametitle{From Term to WT}
  \begin{itemize}
  \item Before we can do type-preserving transformations, we need |WT| terms
  \item The |quoteTerm| keyword first type checks, normalises, then returns |Term| 
  \item Contribution: a translator |Term -> WT| to quote typed lambda terms
  \item Note: compiler modification was necessary here
  \end{itemize}
\end{frame}


\begin{frame}
  \frametitle{What a WT looks like}
\begin{code}
testgoal1 : Raw -- :: (n → n) → n → n
testgoal1 = term2raw (quoteTerm 
    λ (b : ℕ → ℕ) → (λ (x : ℕ) → b x))

typedgoal1 : Well-typed-closed (typeOf testgoal1) _
typedgoal1 = raw2wt testgoal1

seeTG1     :    typedgoal1 
           ≡    Lam       (O Nat => O Nat)
                          (Lam       (O Nat)
                                     (Var (there here) ⟨ Var here ⟩))
seeTG1 = refl
\end{code}
\end{frame}

\subsection{Type-aware framework}

\begin{frame}
  \frametitle{Transformation framework}
  \begin{figure}
    \centering
    \includegraphics[width=\textwidth]{transformation-framework}
    \caption{Possible transitions between representations}
    \label{fig:transition-diagram}
  \end{figure}
\end{frame}


\subsection{Example transformations}

\begin{frame}
  \frametitle{Example 1: Continuation-passing style}
  \begin{itemize}
  \item Control is passed explicitly in the form of a \emph{continuation}
  \item Add extra argument to functions: a continuation
  \item \texttt{return} becomes the continuation
  \item A number of things become explicit:
    \begin{enumerate}
    \item procedure returns, which become apparent as calls to a continuation; 
    \item intermediate values, which are all given names;
    \item order of argument evaluation, which is made explicit;
    \item tail calls, simply calling a procedure with the same continuation, unmodified.
    \end{enumerate}
  \end{itemize}
\end{frame}

\begin{frame}
  \begin{itemize}
  \item Implemented in function |T|
  \item Basically: give abstractions extra argument, the continuation
  \end{itemize}
\begin{spec}
T            : {σ : Uu} {Γ : Ctx}
             → (wt :    WT    Γ                    σ)
             →          WT    (map cpsType Γ)      (cpsType σ => RT)
             →          WT    (map cpsType Γ)      RT
\end{spec}
  
\begin{spec}
cpsType : Uu → Uu
cpsType (O x)         = O x
cpsType (t => t₁)     = cpsType t => (cpsType t₁ => RT) => RT
\end{spec}

\end{frame}

\begin{frame}
  \frametitle{Example of CPS}
  \begin{code}
   original    =    λ g a → g a
   cps         =    T original id
   cps         ≡    (λ f' →
                         (λ e' →
                              f' e' id) a) g
  \end{code}
\end{frame}


\begin{frame}
  \frametitle{Example 2: SKI}
  \begin{itemize}
  \item Extremely simple version of untyped lambda calculus
  \item Only 3 combinators, and application
  \item Elements are closed terms, can be assigned a type
  \item Basically: remove abstractions
  \end{itemize}
  \begin{spec}
S        = λ x y z         → x z (y z)
K        = λ x y           → x
I        = λ x             → x
  \end{spec}

\end{frame}

\begin{frame}
  \frametitle{SKI in Agda}
\begin{spec}
data Comb : Ctx → Uu → Set where
  Var    : ∀ {Γ} → (τ : Uu) → τ ∈ Γ         → Comb Γ τ
  _⟨_⟩   : ∀ {Γ σ τ}
         → Comb Γ (σ => τ) → Comb Γ σ       → Comb Γ τ
  S      : ∀ {Γ A B C}
         → Comb Γ ((A => B => C) => (A => B) => A => C)
  K      : ∀ {Γ A B}                        
         → Comb Γ (A => B => A)
  I      : ∀ {Γ A}                          
         → Comb Γ (A => A)
  
Combinator = Comb []
\end{spec}
\end{frame}

\begin{frame}
  \begin{itemize}
  \item Implemented translation in |compile|
  \item Specialised to closed terms in |topCompile|
  \item Contribution: type-preserving, total, structurally recursive translation
  \end{itemize}
\begin{spec}
topCompile : {τ : U'} → Well-typed-closed τ → Combinator τ
\end{spec}
\end{frame}

\begin{frame}
  \frametitle{Example of SKI}
\begin{code}
const₂       : {α β : Uu} →           Well-typed-closed        (α => β => β) _
const₂       = Lam _ (Lam _ (Var here))

constSKI     : {α β : Uu} →           Combinator               (α => β => β)
constSKI     = K ⟨ I ⟩

seeSKI       : {α β : Uu}    →       topCompile (const₂ {α} {β})
                             ≡       constSKI
seeSKI       = refl
\end{code}
  
\end{frame}


\begin{frame}
  \frametitle{Interim Summary}
  Contributions:
  \begin{itemize}
  \item Type-aware program transformation framework
  \item Examples of use: CPS and SKI
  \item Type-preserving, total, structurally recursive CPS and SKI algorithms
  \end{itemize}
\end{frame}

\section{Discussion}

\begin{frame}
  \begin{itemize}
  \item Illustration of reflection in dependently typed setting
  \item Proof generation
  \item Automatic quoting of user-defined AST 
  \item Type-preserving program transformations
  \pause
  \item \emph{But}, reflection is not yet mature!
    \begin{itemize}
    \item |quote|, |unquote| are keywords
    \item Cannot generate definitions (|data|, functions)
    \item Can only inspect |data| definitions
    \item Type-unaware |unquote|
    \end{itemize}
  \end{itemize}
\end{frame}

\end{document}
%%% Local Variables:
%%% mode: latex
%%% TeX-parse-self: t
%%% TeX-master: t
%%% End: 
