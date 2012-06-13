\documentclass[a4paper]{article}

%include polycode.fmt
%include unicode.fmt
%include agda.fmt

\author{Paul van der Walt \and Wouter Swierstra}
\date{\today}
\title{Proof by reflection by reflection}

\begin{document}

\maketitle


\begin{abstract}
Hi, this is a test.
\end{abstract}


\section{Introduction}

Lorem ipsum dolor sit amet.


\section{Meat}

Here is a sample of some beautiful code.

\begin{code}


module ReflectionProofs where

open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Nat

-- here we have the property of evenness on ℕ
-- zero is even              <- rule
-- n is even => n+2 is even  <- rule
data Even  : ℕ → Set where
  isEvenZ  : Even 0
  isEvenSS : {n : ℕ} → Even n → Even (2 + n)
  
-- we want to prove that 2*n is even, ∀(2*n).

-- therefore, first make a decision function which tells us
-- if a given n is even
even? : ℕ → Bool
even? zero          = true
even? (suc zero)    = false
even? (suc (suc n)) = even? n

-- now prove that n is even precisely when our function
-- returns true
soundnessEven : {n : ℕ} → even? n ≡ true → Even n
soundnessEven {0} refl        = isEvenZ
soundnessEven {1} ()
soundnessEven {suc (suc n)} s = isEvenSS (soundnessEven s)

-- now we can prove instances by applying the soundness theorem
-- with reflexivity proofs

-- For example, it turns out that 28 is even:
isEven28 : Even 28
isEven28 = soundnessEven refl

-- or something which would otherwise have a rather large proof tree
isEven8772 : Even 8772
isEven8772 = soundnessEven refl



\end{code}



\section{Conclusion}


Lorem ipsum dolor sit amet.



\end{document}