\documentclass[usenames,svgnames,dvipsnames,table]{beamer}
%include polycode.fmt
%include agda.fmt
%include generated-colour.fmt
%include codecolour.fmt

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
open import Data.Vec
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


\begin{code}
someTauto2   : (p : Bool)         → P (p ∨ ¬ p)
someTauto2   = quoteGoal e in {!!}
\end{code}
pi
(arg visible
 relevant
 (el (lit 0)
  (def Data.Bool.Bool List.[])))
(el (lit 0)
 (def Proofs.Util.Types.So
  (arg visible
   relevant unknown
   List.∷
   arg visible
   relevant
   (def Data.Bool._∨_
    (arg visible
     relevant
     (var 0 List.[])
     List.∷
     arg visible
     relevant
     (def Data.Bool.¬_
      (arg visible
       relevant
       (var 0 List.[])
       List.∷ List.[]))
     List.∷ List.[]))
   List.∷ List.[])))

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



\begin{frame}[fragile]
\end{frame}




\end{document}