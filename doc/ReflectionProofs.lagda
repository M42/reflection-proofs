\documentclass[a4paper]{article}

%include polycode.fmt
%include unicode.fmt
%include agda.fmt

\newcommand{\ignore}[1]{}

\author{Paul van der Walt \and Wouter Swierstra}
\date{\today}
\title{Proof by reflection by reflection}

\begin{document}

\maketitle


\begin{abstract}
Hi, this is a test.
\end{abstract}


\section{Everything}

Proof by reflection is a technique bla.


The idea behind proof by reflection is that one needn't produce a large proof tree
for each proof instance one wants to have, but rather proves the soundness of
a decision function, in effect giving a ``proof recipe'' which can be instantiated
when necessary.




\ignore{
\begin{code}
module ReflectionProofs where

open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Nat
\end{code}
}


Take for example the property of evenness on natural numbers. One has two
rules (TODO insert rules), namely the rule that says that zero is even, and the
rule that says that if $n$ is even, then $n+2$ is also even.

When translated into an Agda data type, the property of evenness can be expressed
as follows.


\begin{code}
data Even  : ℕ → Set where
  isEvenZ  : Even 0
  isEvenSS : {n : ℕ} → Even n → Even (2 + n)
\end{code}

If one has to use these rules to produce the proof tree each time a
proof of evenness is required for some $N$, this would be tedious.
One would need to unfold the number using |isEvenSS| half the size
of the number. For example, to prove that 6 is even, one would require
the following proof.

\begin{code}
isEven6 : Even 6
isEven6 = isEvenSS (isEvenSS (isEvenSS isEvenZ))
\end{code}

Obviously, this proof tree grows as the natural one would like to show evenness
for becomes larger.

A solution here is to use proof by reflection. The basic technique is as follows.
Define a decision function, called |even?| here, which produces some binary
value (in our case a |Bool|) depending on if the input is true or not.
This function is rather simple in our case.

\begin{code}
even? : ℕ → Bool
even? zero          = true
even? (suc zero)    = false
even? (suc (suc n)) = even? n
\end{code}

Now one can ask whether some value is even or not. Next we need to show that
our decision function actually tells the truth. We need to prove that
|even?| returns |true| iff a proof |Even n| can be produced. This is done in
the function |soundnessEven|. What is actually happening here is that we are
giving a recipe for proof trees such as the one we manually defined for |isEven6|.

\begin{code}
soundnessEven : {n : ℕ} → even? n ≡ true → Even n
soundnessEven {0} refl        = isEvenZ
soundnessEven {1} ()
soundnessEven {suc (suc n)} s = isEvenSS (soundnessEven s)
\end{code}

Now that this has been done, if we need a proof that some arbitrary $n$ is even,
we only need to instantiate |soundnessEven|. Note that the value of $n$ is a hidden
and automatically inferred argument to |soundnessEven|, and that we also pass
a proof that |even? n| returns |true| for that particular $n$. Since in a
dependently typed setting $\beta$-reduction (evaluation) happens in the type system, |refl| is a valid proof. 

\begin{code}
isEven28 : Even 28
isEven28 = soundnessEven refl

isEven8772 : Even 8772
isEven8772 = soundnessEven refl
\end{code}

Now we can easily get a proof that even large numbers are even, without having
to explicitly write down a large proof tree.



\section{Conclusion}


Lorem ipsum dolor sit amet.



\end{document}