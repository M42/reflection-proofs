\documentclass[usenames,svgnames,dvipsnames,table]{beamer}
%include polycode.fmt
%include agda.fmt
%include generated-colour.fmt
%include codecolour.fmt

\usepackage[T1]{fontenc}

\usetheme{Berlin}
\newcommand{\ignore}[1]{}

\ignore{
\begin{code}
module slides.Colloquium where
\end{code}
}

\title{Reflection in Agda}
\author[Paul van der Walt]{Paul van der Walt}
\institute[Dept. CS @@ UU.nl]{Supervisors: Wouter Swierstra and Johan Jeuring\\ Department of Computing Science, Utrecht University}
\date{4$^{\text{th}}$ of October, 2012}

\begin{document}


\begin{frame}
\maketitle
\end{frame}

\section{Introduction}



\begin{frame}
  \frametitle{Introduction}
  Test
\end{frame}


\section{Definitions}

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

\end{frame}


\begin{frame}
  \frametitle{Proof by Reflection}
  
\end{frame}




\begin{code}
even? : ℕ → Set
even? 0                 = ⊤
even? 1                 = ⊥
even? (suc (suc n))     = even? n
\end{code}
\begin{code}
soundnessEven : (n : ℕ) → even? n → Even n
soundnessEven 0              tt        = isEven0
soundnessEven 1              ()
soundnessEven (suc (suc n))  s         = isEven+2 (soundnessEven n s)
\end{code}
\begin{code}
isEven28        : Even 28
isEven28        = soundnessEven 28 tt

isEven8772      : Even 8772
isEven8772      = soundnessEven 8772 tt
\end{code}
\ignore{
\begin{code}
open import Proofs.Util.Lemmas
open import Proofs.TautologyProver renaming (soundness to soundnessImplicit)

soundness       : {n : ℕ} → (b : BoolExpr n) → foralls b
                → proofGoal n b
soundness  b p  = soundnessImplicit b {p}
\end{code}
}

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
\begin{spec}
Env   : ℕ → Set
Env   = Vec Bool
\end{spec}
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
\begin{spec}
someTauto    : (p q : Bool)         → P( p ∧ q ⇒ q )
someTauto    = (HOLE 0)
\end{spec}


\begin{spec}
soundness       : {n : ℕ} → (b : BoolExpr n) → foralls b
                → proofGoal n b
\end{spec}


\begin{code}
rep          : BoolExpr 2
rep          = Imp    (And (Atomic (suc zero)) (Atomic zero)) 
                      (Atomic zero)

someTauto    : (p q : Bool)         → P( (p ∧ q) ⇒ q )
someTauto    = soundness rep _
\end{code}

but duplication!!


\begin{spec}
someTauto2   : (p : Bool)         → P (p ∨ ¬ p)
someTauto2   = quoteGoal e in (HOLE 0)
\end{spec}

\begin{spec}
e ≡    pi (... Bool...) -- intro variable p
          (def So (arg (def _∨_ (   arg (var 0 []) ∷
                                    arg (def ¬_  (arg     (var 0 [])
                                    ∷ [])) ∷ [])) ∷ []))
\end{spec}

\begin{code}
someTauto2   : (p : Bool)         → P (p ∨ ¬ p)
someTauto2   = quoteGoal e in proveTautology e
\end{code}



\ignore{
\begin{code}

open import Data.Sum
open import Data.Product
open import Reflection
open import Metaprogramming.Autoquote renaming (_#_↦_ to _\#_↦_)

\end{code}
}
autoquote, another contribution.
\begin{code}
boolTbl : Table BoolIntermediate
boolTbl =   (Atomic ,
                  2 \# (quote _∧_      ) ↦ And
            ∷     2 \# (quote _∨_      ) ↦ Or
            ∷     1 \# (quote  ¬_      ) ↦ Not
            ∷     0 \# (quote true     ) ↦ Truth
            ∷     0 \# (quote false    ) ↦ Falsehood
            ∷     2 \# (quote _⇒_      ) ↦ Imp ∷ [])

term2bool_auto     : (t : Term)
                   → {pf : convertManages boolTbl t}
                   → BoolIntermediate
term2bool_auto t {pf} = doConvert boolTbl t {pf}
\end{code}
\ignore{
\begin{code}
open import Metaprogramming.ExampleUniverse
open DT hiding (Well-typed-closed) renaming (U' to Uu) 
open import Metaprogramming.Util.Equal
\end{code}
}


* refresher: what is De Bruijn representation

\begin{table}[h]
  \centering
  \begin{tabular}{c||c}
    Named & De Bruijn \\
    \hline
    $\lambda x . x$ & $\lambda . 0$\\
    $\lambda x . \lambda y . x y$ & $\lambda . \lambda . 1~0$\\
    \end{tabular}
  \caption{A few sample translations from named lambda terms to De Bruijn-indexed terms.}\label{tab:debruijn}
  \end{table}
  

Term only has annotations on the variable bindings -- we check that
the term is well-typed and produce a |WT|.
Once we have a |WT|, we can do type-preserving tranformations
on lambda terms.

initially no annotations though -- contribution to compiler's code.


  
\begin{code}
data WT' : Ctx → Uu → Set where
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

examples:
* CPS (explain what that is, plus example)
* SKI (also explain)

- give type signatures of compile and T...

* contribution here:
 > type-preserving transformation framework
 > total, structurally recursive, type-safe CPS
 > total, structurally recursive, type-safe SKI


\ignore{
\begin{code}
open import Relation.Binary.PropositionalEquality
open SKI'
\end{code}}

\begin{spec}
data Comb : Ctx → Uu → Set where
  Var    : ∀ {Γ} → (τ : Uu) → τ ∈ Γ         → Comb Γ τ
  _⟨_⟩   : ∀ {Γ σ τ}
         → Comb Γ (σ => τ) → Comb Γ σ       → Comb Γ τ
  S      : ∀ {Γ A B C}
         → Comb Γ ((A => B => C) => (A => B) => A => C)
  K      : ∀ {Γ A B}                        → Comb Γ (A => B => A)
  I      : ∀ {Γ A}                          → Comb Γ (A => A)
  
Combinator = Comb []
\end{spec}

\begin{spec}
topCompile : {τ : U'} → Well-typed-closed τ → Combinator τ
\end{spec}

\begin{code}
const₂       : {α β : Uu} →           Well-typed-closed        (α => β => β) _
const₂        = Lam _ (Lam _ (Var here))

constSKI     : {α β : Uu} →           Combinator               (α => β => β)
constSKI     = K ⟨ I ⟩

see          : {α β : Uu}    →       topCompile (const₂ {α} {β})
                             ≡       constSKI
see          = refl
\end{code}

\begin{spec}
cpsType : U' → U'
cpsType (O x)     = O x
cpsType (t => t₁) = cpsType t => (cpsType t₁ => RT) => RT
\end{spec}

\begin{spec}
T            : {σ : U'} {Γ : Ctx}
             → (wt :    WT    Γ                    σ                   )
             →          WT    (map cpsType Γ)      (cpsType σ => RT)
             →          WT    (map cpsType Γ)      RT
\end{spec}
insert diagram of well-typed things here?

\begin{frame}
  \frametitle{Decision Function}
  
\end{frame}

\begin{frame}
  \frametitle{Soundness}
  
\end{frame}

\begin{frame}
  \frametitle{Usage}
  
\end{frame}

\begin{frame}
  \frametitle{Argh, duplication!}
  
\end{frame}






\end{document}