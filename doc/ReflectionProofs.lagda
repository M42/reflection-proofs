\documentclass{llncs}


\usepackage{color}
\usepackage[usenames,dvipsnames,svgnames,table]{xcolor}

%% the newcode stuff is for code extraction.

%include polycode.fmt
%if style == newcode
%else
%include agda.fmt
%include generated-colour.fmt
%include codecolour.fmt
%endif


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% microtype with settings.
\usepackage[activate={true,nocompatibility},final,tracking=true,kerning=true,spacing=true,factor=1100,stretch=10,shrink=10]{microtype}
\microtypecontext{spacing=nonfrench}
%% end DRAFT-version stuff. }}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage{subfigure}
\usepackage{xspace}
\usepackage{textcomp} % text-mode <> characters

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% Font definitions.
\usepackage{tgpagella}                  %% looks a little like palatino -- thanks Zapf!
\usepackage[T1]{fontenc}
\usepackage{savesym}

\usepackage{amsmath}
\savesymbol{iint}
\restoresymbol{TXF}{iint}
\renewcommand{\ttdefault}{lmtt}         %% Latin Modern for teletype
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\pagestyle{plain}

\newcommand{\ignore}[1]{}

\newcommand{\ghloc}{https://github.com/toothbrush/reflection-proofs}
\newcommand{\ghurl}{\url{\ghloc}}
\def\CC{{C\nolinebreak[4]\hspace{ -.05em}\raisebox{.2ex}{\small\bf ++}}}
\colorlet{hlite}{CornflowerBlue!15!white}
%\colorlet{hlite}{black!15!white}

\newcommand{\hlitem}[1]{\item[\colorbox{hlite}{#1}]~\\}
\newcommand{\ch}{Curry--Howard isomorphism\xspace}
\usepackage{adjustbox}

%%%%%%%%%%%%%%%%%%
% make figures a little more snug
\setlength{\textfloatsep}{0.5\baselineskip plus 0.2\baselineskip minus 0.2\baselineskip}
\setlength{\intextsep}{0.5\baselineskip plus 0.2\baselineskip minus 0.2\baselineskip}
%%%%%%%%%%%%%%%%%%

\newenvironment{shadedfigure}[1][tbhp]{%
    \begin{figure}[#1]%
    \begin{adjustbox}{minipage=\linewidth-10pt,margin=5pt,bgcolor=hlite}%
}{%
    \end{adjustbox}%
    \end{figure}%
}
\newenvironment{shade}{%
%
\vskip 0.2\baselineskip%
\begin{adjustbox}{%
minipage=\linewidth,margin=0pt,padding=0pt,bgcolor=hlite%
}}{%
\end{adjustbox}%
\vskip 0.2\baselineskip%
%
}

\ignore{
\begin{code}
module doc.ReflectionProofs where

open import Proofs.TautologyProver hiding (concrete2abstract;  soundness ;
        boolTable;  proofGoal ;  forallsAcc )
open import Data.Bool renaming (not to ¬_)
open import Relation.Binary.PropositionalEquality
open import Reflection
open import Data.List
open import Data.Nat
open import Data.Unit using (⊤ ; tt)
open import Data.Empty
open import Data.Product
open import Data.Maybe
open import Data.Vec
open import Relation.Nullary using (yes; no)
open import Data.String
open import Data.Fin hiding (_+_) renaming (zero to Fzero ; suc to Fsuc)
open import Proofs.Util.Types
open import Proofs.Util.Lemmas
open import Proofs.Util.Types using (Diff; Base; Step)


\end{code}
}

%\usepackage[numbers,sort&compress]{natbib}
\newcommand{\citep}[1]{\cite{#1}}
\usepackage{hyperref}

%%%%% Give citations etc a nicer look
\hypersetup{
  colorlinks,
  citecolor=black,
  linkcolor=black,
  urlcolor=black}
%%%%%%%%%%%%%%%%
\usepackage{url}



\date{\today}
\title{Engineering Proof by Reflection in Agda}
\author{Paul van der Walt \and Wouter Swierstra}
\newcommand{\myemail}{paul@@denknerd.org}
\institute{
Department of Computer Science, Utrecht University, The Netherlands\\
\href{mailto:\myemail}{\nolinkurl{\myemail}}, \href{mailto:w.s.swierstra@@uu.nl}{\nolinkurl{w.s.swierstra@@uu.nl}}
}

\begin{document}

\maketitle

\begin{abstract}
  This paper explores the recent addition to Agda enabling
\emph{reflection}, in the style of Lisp and Template Haskell.
It gives a brief introduction to using reflection, and details the complexities encountered when
  automating certain proofs with \emph{proof by
  reflection}. 
It presents a library that
can be used for automatically quoting a class of concrete Agda terms
to a non-dependent, user-defined
inductive data type, alleviating some of the burden a programmer faces
when using reflection in a practical setting. 
\keywords{dependently-typed programming, reflection, Agda, proof by
  reflection, metaprogramming}
\end{abstract}

\newcommand{\researchquestion}{%
\begin{quote}%
  ``What practical issues do we run into when trying to engineer
  automatic proofs in a dependently typed language with reflection?
  Are Agda's reflective capabilities sufficient and practically
  usable, and if not, which improvements might make life easier?''
\end{quote}%
}%

\section{Introduction}\label{chap:introduction}

The dependently typed programming language
Agda~\citep{norell:thesis,Norell:2009:DTP:1481861.1481862} has recently been
extended with a \emph{reflection mechanism}~\cite{vdWalt:Thesis:2012} for compile time metaprogramming in the style of Lisp~\cite{lisp-macros},
MetaML~\cite{metaml}, Template Haskell~\cite{template-haskell}, and
\CC\ templates%~\cite{cplusplus}
. Agda's reflection mechanisms make it
possible to convert a program fragment into its corresponding abstract
syntax tree (AST) and vice versa. In tandem with Agda's dependent types,
this has promising new programming potential.

This paper addresses the following central questions:

\researchquestion

\paragraph{Contributions.} This paper reports on the experience of using Agda's reflection mechanism to automate certain 
categories of proofs.
This is a case study,
illustrative % reviewer 4: "exemplative => illustrative"
of the kind of problems that can be solved using
reflection. More specifically:

\begin{itemize}
  \item We give a very brief introduction to Agda's reflection mechanism
(Sec.~\ref{sec:crash}). Previously, these features were only
documented in the release notes and comments in Agda's source
files. A detailed tutorial is available elsewhere~\cite{vdWalt:Thesis:2012}.
\item We present |Autoquote|, an Agda library that does a
  declaratively-specified 
  translation of a quoted
expression to
a representation in a user-defined non-dependent datatype 
(Sec.~\ref{sec:autoquote}).
\item We show how to use Agda's reflection mechanism to
  automate certain categories of proofs (Sec.~\ref{sec:proof-by-reflection}).
 The idea of \emph{proof by
    reflection} is certainly not new, but still worth examining in the
  context of this technology. % removed keyword new, as per reviewer 2
\end{itemize}
The code presented in this paper compiles using 
 Agda version 2.3.2.\footnote{All supporting code, including this
paper in Literate Agda format, is available on
GitHub. \ghurl} %
% review comment applied: paper isn't Literate Agda

\subsection{Introducing Agda}\label{sec:reflection}

Agda is an implementation
of Martin-L\"of's type theory~\cite{Martin-Lof:1985:CMC:3721.3731},
extended with records and modules. It is developed at the Chalmers
University of Technology~\cite{norell:thesis}; in accordance with \ch,
it can be viewed as
both a 
functional programming language
and a proof assistant for intuitionistic logic. It is comparable to
Coq, which is based on
Coquand's calculus of constructions~\cite{DBLP:journals/iandc/CoquandH88}. 
There are many excellent tutorials
 on Agda~\citep{norell:thesis,Norell:2009:DTP:1481861.1481862,Oury:2008:PP:1411204.1411213}.

Since version 2.2.8, Agda includes a reflection API~\cite{agda-relnotes-228}, which allows the conversion of
parts of a program's code into an abstract syntax tree, a data structure
in Agda itself, that can be inspected or modified like any other.
The idea of reflection is old: in the 1980s % no apostrophe!
 Lisp included a similar
feature, then already called \emph{quoting} and \emph{unquoting},
which allowed run time modification of a program's code.
 %This has given rise to powerful techniques for code reuse and
%abstraction.

\section{Using Reflection}\label{sec:crash}

We will now introduce the reflection API with some small examples.
%%% redundancy removed:
% This is by no means a comprehensive
% tutorial; instead, one can be found in \cite{vdWalt:Thesis:2012}.

\paragraph{The Keywords.} There are several keywords that can be used to quote and unquote
terms:         |quote|, |quoteTerm|, |quoteGoal|, and |unquote|. The
|quote| keyword allows the user to access the internal representation of
any identifier. This internal representation, a |Name| value, can be used to query the
type or definition of the identifier. We refer to the release
notes~\cite{agda-relnotes-228} for a listing of the data structures
involved; most important is |Term : Set|, 
representing concrete Agda terms.

The simplest example of quotation uses the keyword |quoteTerm x : Term|, where |x| is a fragment of concrete syntax.  Note that
|quoteTerm| reduces like any other function in Agda. As an
example, the following unit test type checks:

\begin{shade}
\begin{code}
example₀   : quoteTerm (\ (x : Bool) -> x)       ≡ lam visible (var 0 [])
example₀   = refl
\end{code}
\end{shade}

In dissecting
this,  we find the |lam|
constructor, since we introduced a lambda abstraction. Its one argument is visible (as opposed to implicit), and
the body of the lambda abstraction is just a reference to the
nearest-bound variable, thus |var 0|, applied to an empty list of
arguments. Variables are referred to by their De Bruijn indices.

Furthermore, |quoteTerm| type checks its argument before
returning the |Term|. Since
type checking a term necessitates normalisation, the returned |Term| is
always in normal form, as |example₁| demonstrates.

\begin{shade}
\begin{code}
example₁   : quoteTerm ((\ x → x) 0) ≡ con (quote zero) []
example₁   = refl
\end{code}
\end{shade}

The identity function is applied to zero, resulting in just the value zero.
The quoted representation of a natural zero is |con (quote zero) []|, where |con| means that we
are introducing a constructor. The constructor |zero| takes no arguments, hence the empty list.

The |quoteGoal| keyword is different. We cannot
assign |quoteGoal| an informal type, since it is really a
syntactic construct that depends on the context. See the following example.

\begin{shade}
\begin{spec}
example₂ : ℕ
example₂ = quoteGoal e in (HOLE 0)
\end{spec}
\end{shade}

The |quoteGoal| keyword binds the variable |e| to the |Term|
representing the type expected at the position of |quoteGoal|. In this example, the value
of |e| in the hole will be |def ℕ []|, i.e., the |Term| representing
the type |ℕ|, which is a definition, hence |def|.

The |unquote| keyword 
 takes one argument -- a |Term|  -- and converts it back to a concrete
expression. Just as |quoteTerm| and |quoteGoal|, |unquote| type checks and
normalises the |Term| before splicing it into the program text. Note that it is not yet possible to introduce top-level declarations
using |unquote|. This is a technical limitation.

The
|quote x : Name| keyword returns the representation of an identifier |x| as a value in the
primitive type |Name|, if |x| is the name of a definition (function, datatype, record, or
      a constructor).
Unfortunately, we cannot simply pattern match on constructor names. The reason pattern matching on
|Name|s is not supported, is that the elimination principle is not clear, since |Name| is a built-in, non-inductive type. 
 The only mechanism we have to distinguish |Name|s is
decidable equality\footnote{using the function |_≟-Name_|}, which results in code as presented below -- a lot
less concise than the pattern matching equivalent would be.
 Agda does allow matching on |String|s
(which similarly only expose decidable equality), so the
limitation is a technical one, which might be solved in the future.
% Note that since we want a |case|-like decision here, many
% nested branches will be necessary. 

\begin{shade}
\begin{spec}
whatever : Term → ...
whatever (con c args) with c ≟-Name quote foo
...                   | yes p     = (HOLE 0) -- |foo| applied to arguments
...                   | no ¬p     = (HOLE 1) -- not |foo|, try another |Name|, etc.
\end{spec}
\end{shade}


This short introduction should already be enough to start developing
simple programs using reflection.  For a more detailed description of
the reflection API in Agda, the reader is referred to  Van
der Walt's thesis~(\cite{vdWalt:Thesis:2012}, Chapter~3).

\section{Automatic Quoting}\label{sec:autoquote}
\ignore{
\begin{code}
open import Metaprogramming.Autoquote
\end{code}
}

In the previous section, we saw how to recover values of type
|Term|, representing concrete Agda terms. This is a start, but
we rarely want to directly manipulate |Term|s: often it
is much more useful to use our own AST for computations. It should
be a minor task to write a function to convert a |Term|
into another AST, but this often turns out to become a mess.

When  pattern matching is possible, converting
elements of one AST to another is a simple
task. Unfortunately, Agda functions are required to be
total, which means they must have a case for each possible pattern. Since  |Term|
 covers all quotable terms, it has many alternatives.  Furthermore,
 for |Name|s, we only have decidable
equality. This is why
 such 
 conversion functions tend to become
verbose, as in the code snippet of
Fig.~\ref{fig:concrete2abstract}, an excerpt of a
conversion function used before a better solution was developed.

\begin{shadedfigure}
\begin{spec}
term2boolexpr n (con tf []) pf with tf ≟-Name quote true
term2boolexpr n (con tf []) pf | yes p = Truth
...
term2boolexpr n (def f []) ()
term2boolexpr n (def f (arg v r x ∷ [])) pf with f ≟-Name quote ¬_
... | yes p = Not (term2boolexpr n x pf)
... | no ¬p with f ≟-Name quote _∧_
...
\end{spec}
\caption{The gist of a na\"ive conversion function, from |Term| into some more specific data
  type.}\label{fig:concrete2abstract}
\end{shadedfigure}

A (partial) solution -- something which at least mitigates 
the agony -- is presented in this section, in the form of the
|Autoquote| library.

\paragraph{The |Autoquote| Library.} %
We will use |Expr|, presented in Fig.~\ref{fig:exprdata}, as a running
example of a toy AST.
It is a simple non-dependent inductive data structure representing terms with Peano-style natural
numbers, variables represented using De Bruijn indices, and additions.


\begin{shadedfigure}
\begin{code}
data Expr : Set where
  Var           : ℕ               →     Expr
  Plus          : Expr → Expr     →     Expr
  S             : Expr            →     Expr
  Z             :                       Expr
\end{code}
\caption{The toy expression language |Expr|. Quoting such terms is now easier.}\label{fig:exprdata}
\end{shadedfigure}

We might want to convert an expression, such as $5 + x$, to this AST
using reflection. In an ideal world, we would just pattern match on
concrete constructs such as the |_+_| function and return elements
like |Plus| of our AST.  The |Autoquote| library allows just this,
exposing an interface which, when provided with such a mapping,
automatically quotes expressions that fit. Here, \emph{fitting} is
defined as only containing names that are listed in the mapping, or
variables with De Bruijn indices, and respecting constructor
arities. Trying to convert other terms results in a type error.  The
user provides a straightforward mapping, such as in % elegant => straightforward, review 4 
Fig.~\ref{fig:exprTable}, and |Autoquote|
converts Agda terms to values in the AST. Currently only non-dependent
inductive types are supported.

\begin{shadedfigure}
\begin{code}
exprTable : Table Expr
exprTable = (  Var ,    (quote _+_     )   ↦ Plus   ∷
                        (quote zero    )   ↦ Z      ∷ 
                        (quote suc     )   ↦ S      ∷ [])
\end{code}
\caption{The mapping table for converting to the |Expr| AST. }\label{fig:exprTable}
\end{shadedfigure}

This table should be interpreted as follows: any variables encountered
should be stored in |Var|s, and
the |_+_| operator should be mapped to a |Plus| constructor. 
A |zero|, from the |Data.Nat| standard library, should be treated as our |Z| constructor, etc.
 Note that the first item in the table
(|Var| in this case) is special, and should be a constructor for De
Bruijn-indexed variables. The rest of the table is an arbitrary list of constructors.

We will not say much about the implementation of this library, since
it is not groundbreaking.
For more details, we again refer to (\cite{vdWalt:Thesis:2012}, Sec.~3.3). 
Using the library is simple; it exposes a function called
|doConvert| which takes the conversion table, a (hidden, automatically
inferred)  proof that
the conversion is possible, and a |Term| to convert,
and produces an inhabitant of the desired data type, where
possible. The implicit proof technique is outlined in
Sec.~\ref{sec:implicit}. 

The use of |doConvert| is illustrated in Fig.~\ref{fig:test-autoquote}. 
The hidden assumption that the conversion is possible causes
a 
type error if an incompatible term is given.
The utility of the |Autoquote| library is clear if you
compare this relatively straightforward code  to the verbose
|term2boolexpr| snippet in Fig.~\ref{fig:concrete2abstract}.


\begin{shadedfigure}
\begin{code}
example₃ : {x : ℕ}      → doConvert    exprTable      (    quoteTerm (x + 1))
                        ≡                                  Plus (Var 0) (S Z)
example₃ = refl
\end{code}
\caption{An example of |Autoquote| in use. See Fig.~\ref{fig:exprTable} for the definition of |exprTable|, a declarative |Name|-to-constructor mapping.}\label{fig:test-autoquote}
\end{shadedfigure}

Usually, the result from |doConvert| will require some
post-processing -- 
for example, turning all
naturals into |Fin n| values, or scope checking a resulting
expression -- as we will see in the Boolean tautologies example
(Sec.~\ref{sec:Boolean-tautologies}). However, for now it suffices to
say that |Autoquote| eases converting |Term|s into other ASTs.

A mechanism like |Autoquote| is actually an ad-hoc workaround for a more
general difficulty in Agda, namely that currently, a watered-down
version of pattern matching on data types
exposing decidable equality is  unreasonably awkward. If this were
possible in general, like it is for |String|, the |Autoquote|
library would be redundant.

\section{Proof by Reflection}\label{sec:proof-by-reflection}

The idea behind proof by reflection is simple: given that type theory
is both a programming language and a proof system, it is possible to
define functions that compute proofs. 
% Reflection is an overloaded word
% in this context, since in programming language technology reflection
% is the capability of converting some piece of concrete code
% into an abstract syntax tree that can be manipulated in the same
% system. 
Reflection in the proof technical sense is the method of
mechanically constructing a proof of a theorem by inspecting its
shape. The proof by reflection technique we describe here is not new --
see for example Chapter~16 of Coq'Art~\cite{L:BC04} -- but
instead
combines a number of existing methods into a usable package. 
The following two case studies illustrate proof by
reflection and how Agda's reflection mechanism can make the technique
more accessible. The first example is a closed example and  sets the
stage for the second, an open expression type extended to include variables.


\subsection{Closed Example: Evenness}\label{sec:evenness}

To illustrate the concept of proof by reflection, we will follow
Chlipala's example of even naturals~\cite{chlipala2011certified}. 
%%It will serve as a stepping stone for the example in
%%Sec.~\ref{sec:Boolean-tautologies}.
Our objective is to be able to automatically prove evenness of certain naturals. To this end, we first write a 
test function which decides if a natural is even, then prove the
soundness of this predicate. This results in a proof generator. 

 We start by defining the
property |Even|.

\begin{shade}
\begin{code}
data Even      : ℕ → Set where
  isEven0      :                          Even 0
  isEven+2     : {n : ℕ} → Even n     →   Even (2 + n)
\end{code}
\end{shade}

Using these rules to produce the proof that some large number $n$ is
even is tedious: it requires $n/2$
applications of the |isEven+2| constructor.

To automate this, we will show how to \emph{compute} the proof
required. We define a predicate |even?| that
returns the unit type (top) when its input is even and the empty type (bottom) otherwise.
In this context, |⊤| and |⊥| can be seen as the analogues of |true|
and |false|, since
 there exists
a proof that some number is even, if it is $0$ or $2 + n$, for even $n$. Otherwise, no proof exists. 
% The idea
% of ``there exists'' is perfectly modelled by the unit and empty types. 

\begin{shade}
\begin{code}
even? : ℕ → Set
even? 0                 = ⊤
even? 1                 = ⊥
even? (suc (suc n))     = even? n
\end{code}
\end{shade}

Next we need to show that the |even?| function is \emph{sound}.
 To do so, we prove that if and only if |even? n| returns |⊤|,
the type |Even n| is
inhabited. Since we are working in a constructive logic, the only
way to show this is to give a witness. This is done in the function |soundnessEven|. Note that
we are 
actually giving a recipe for
constructing proof trees.

\begin{shade}
\begin{code}
soundnessEven : {n : ℕ} → even? n → Even n
soundnessEven {0}              tt        = isEven0
soundnessEven {1}              ()
soundnessEven {suc (suc n)}    s         = isEven+2 (soundnessEven s)
\end{code}
\end{shade}

In the case of $n=1$, we do not need to provide a
right-hand side of the function definition. The assumption |even?
1| is uninhabited, and we discharge this branch using Agda's
absurd pattern, \texttt{()}.

If we need a proof that some arbitrary
|n| is even, |soundnessEven| builds it. Note that
the value of |n| is inferred. The only
argument we must to provide to |soundnessEven| is  proof
that |even? n| is inhabited. For any closed term, such as the numbers |28|
or |8772|, this proof obligation reduces to 
|⊤|, which is proven by its single constructor, |tt|.

\begin{shade}
\begin{code}
isEven8772      : Even 8772
isEven8772      = soundnessEven tt
\end{code}
\end{shade}

Now we can easily get a proof term for arbitrary even numbers,
without having to explicitly write down the proof tree. Note that
it is not possible to give a term with type |Even 27|, or any other uneven
number, since the parameter |even? n|  is equal to |⊥|,
 which is uninhabited.
Providing |tt| anyway will
produce a type error stating that the types |⊤| and |⊥| cannot be unified.

\paragraph{Implicit Proofs.}\label{sec:implicit} Since the type |⊤| is a simple record type, Agda can infer the |tt|
argument. This means we can turn the assumption |even? n| into an
implicit argument, so a user could just write 
|soundnessEven| as the proof, letting Agda fill in the missing proof. 
This trick works
because Agda supports eta expansion for record types. 
Concretely, Agda will automatically fill in implicit arguments of
the unit type. Here, the type system is doing more work than
 for general
 data types; for records eta expansion is safe, since recursion is not allowed.
This trick  will be
used from here on to ameliorate  our proof generators' interfaces.

\paragraph{Friendlier Errors.}  It is possible to generate a descriptive ``error'' of
sorts, by replacing the |⊥| with
an empty type that has a friendly name:

\begin{shade}
\begin{spec}
data IsOdd : ℕ -> Set where
\end{spec}  
\end{shade}

This makes the soundness proof a little less straightforward, but in return the
type error generated if an odd number is used becomes more
informative. When a user tries to use the |soundnessEven| lemma to generate a proof
of the statement |Even 7|, Agda will complain about a missing implicit
argument of type |IsOdd 7|. An unsolved implicit argument is marked
yellow in Agda, which looks less dire than a type error in a visible argument, but 
no spurious proofs are being generated.


\paragraph{Limitations.} This is a very simple, closed example. In particular, it would not work in the
presence of quantifications, for example to define a lemma like |Even x -> Even (x + 100)|. 
Why this is the case, and how it could be solved, is discussed at the end of Sec.~\ref{para:limi}.

The next step will be to use the same approach for a problem involving variables.




\subsection{Open Example: Boolean Tautologies}\label{sec:Boolean-tautologies}

We will now apply the same steps as above to a different problem, clarifying
the relationship to the previous example  at each step.
This example of proof by reflection will be lifting a predicate
that checks if a Boolean expression with indexed variables is a tautology under all possible
assignments, to a proof generator. 

Take as an example the following proposition.
\begin{align}\label{eqn:tauto-example}
(p_1 \vee q_1) \wedge (p_2 \vee q_2) \Rightarrow (q_1 \vee p_1) \wedge (q_2 \vee p_2)
\end{align}

If we squint, we see that \eqref{eqn:tauto-example} is a tautology, but explicitly proving this 
in Agda would be rather tedious. Assuming we want to check if the formula always holds by
trying all possible variable assignments, this would require $2^n$
pattern matching cases, where $n$ is the number of variables.

To automate this process, we  start by defining an
inductive data type to represent Boolean expressions with at most $n$ free
variables (see Fig.~\ref{fig:boolexprn}).

\begin{shadedfigure}
\begin{spec}
data BoolExpr (n : ℕ) : Set where
  Truth Falsehood  :                                  BoolExpr n
  And   Or  Imp    : BoolExpr n → BoolExpr n      →   BoolExpr n
  Not              : BoolExpr n                   →   BoolExpr n
  Atomic           : Fin n                        →   BoolExpr n
\end{spec}
\caption{Modelling Boolean expressions with $n$ free variables.}\label{fig:boolexprn}
\end{shadedfigure}

We use the type |Fin n| to ensure
that variables (represented by |Atomic| and identified by their De Bruijn index) are in scope. If we want to
evaluate the expression, we will need some way to map variables to values.
For this we use |Env n|: a vector of $n$ Boolean values. %, since a |BoolExpr n| has at most $n$ free variables.

Now we can define an interpretation function, which tells us if an
 expression is true or not, given some assignment of variables. It does this by evaluating
the formula's % the apostrophe is bonafide.
 AST, filling in for |Atomic| values the concrete values which are
looked up in the environment. For example, |And| is evaluated to
the Boolean function |_∧_|, and its two arguments in turn are
recursively interpreted.

\ignore{
\begin{code}
open import Proofs.Util.Handy
\end{code}
}

\begin{shade}
\begin{spec}
⟦_⊢_⟧ : ∀ {n : ℕ} (e : Env n) → BoolExpr n → Bool
⟦ env     ⊢ Truth           ⟧ = true
⟦ env     ⊢ And   be   be₁  ⟧ =     ⟦ env ⊢ be ⟧     ∧      ⟦ env ⊢ be₁ ⟧
⟦ env     ⊢ Atomic n        ⟧ = lookup n env
...
\end{spec}
\end{shade}

Recall our test function |even?| in the previous section. It returned
|⊤| if the proposition was valid, |⊥| otherwise. Looking at |⟦_⊢_⟧|, we see that
we should just translate |true| to the unit type and |false| to the empty type, to get
the analogue of the |even?| function. We therefore define a function
|P|, mapping Booleans to types (see Fig.~\ref{fig:error}). As before
we decorate the empty type, this time with a string, to give more
informative error messages.

\begin{shadedfigure}
\begin{spec}
data Error (e : String) : Set where 

P    : Bool → Set
P  true    =     ⊤
P  false   =     Error "Argument expression does not evaluate to true."
\end{spec}
\caption{Empty type |Error|, facilitating clearer errors.}\label{fig:error}
\end{shadedfigure}

Now that we have these helper functions, it is easy to define what it
means to be a tautology. We quantify over a few Boolean variables and
wrap the formula in the function |P|. If the resulting type is
inhabited, the argument to |P| is a tautology, i.e., for each
assignment of the free variables the entire equation still evaluates
to |true|. An example encoding of such a theorem is Fig.~\ref{fig:exampletheorem}~-- notice
how similar it looks to the version expressed in mathematical notation, in~\eqref{eqn:tauto-example}.

\begin{shadedfigure}
\begin{code}
exampletheorem = (p₁ q₁ p₂ q₂ : Bool)   →
                 P  (         (p₁ ∨ q₁) ∧ (p₂ ∨ q₂) ⇒ (q₁ ∨ p₁) ∧ (q₂ ∨ p₂))
\end{code}
\caption{The term |exampletheorem : Set| encodes \eqref{eqn:tauto-example}.}\label{fig:exampletheorem}
\end{shadedfigure}

Here a complication arises, though. We are quantifying over a list of Boolean values \emph{outside}
of the function |P|, so proving |P| to be sound will not suffice. We just defined the function |⟦_⊢_⟧|
to take one environment and one expression. In Fig.~\ref{fig:exampletheorem}, though,
we effectively quantified over all possible environments. We are going to need a way
to lift the function |P| over arbitrary environments.

% Ik zou uitkijken met het gebruik van 'decision function' -- hier
% wordt meestal mee bedoeld een functie van het type:
% decideP : (x : A) -> Either (P x) (P x -> Empty)

The function |forallsAcc|, in Fig.~\ref{fig:forallsacc}, performs this lifting. This function represents the real analogue
of |even?| in this situation: it returns a type which is only inhabited if the argument Boolean
expression is true under all variable assignments. This is done by cumulatively generating a full binary tree -- the truth table --
of |⊤| or |⊥| types, depending on the result of |⟦_⊢_⟧| under each assignment.
This corresponds precisely to the expression being a tautology if and
only if the tree is inhabited. The function |foralls| simply bootstraps
|forallsAcc| with an empty environment -- it is omitted for brevity.
The |Diff| argument makes |forallsAcc| produce a
tree with depth equal to the number of free variables in an
expression, putting  a bound on the recursion. 

\begin{shadedfigure}
\begin{code}
forallsAcc : {n m : ℕ} → BoolExpr m → Env n → Diff n m → Set
forallsAcc b acc    (Base     ) = P ⟦ acc ⊢ b ⟧
forallsAcc b acc    (Step y   ) =
  forallsAcc b (true ∷ acc) y × forallsAcc b (false ∷ acc) y
\end{code}
\caption{The function |forallsAcc|, which decides if a proposition is a tautology. Compare to the |even?| function in Sec.~\ref{sec:evenness}.}\label{fig:forallsacc}
\end{shadedfigure}

\paragraph{Soundness.} Now we finally know our real decision function |foralls|, we can set about proving its
soundness. Following the |soundnessEven| example, we want a function with a type something like in Fig.~\ref{fig:informal-soundness}.

\begin{shadedfigure}
\begin{spec}
soundness : {n : ℕ} → (b : BoolExpr n) → foralls b → ...
\end{spec}
\caption{The informal type of |soundness|, taking an expression and its truth table.}\label{fig:informal-soundness}
\end{shadedfigure}

But what should the return type of the |soundness| lemma be? We would like to
prove that the argument |b| is a tautology, and hence, the |soundness|
function should return something of the form |(b₁ ... bn : Bool) -> P
B|, where |B| is an expression in the image of the interpretation
|⟦_⊢_⟧|. For instance, the statement |exampletheorem| is a proposition
of this form.

The function |proofGoal| takes a |BoolExpr n| as its argument and generates the proposition
that the expression is a tautology, by giving back the type  equal to the theorem  under scrutiny. It 
first introduces $n$ universally quantified Boolean
variables. These variables are accumulated in an environment. Finally, when $n$
binders have been introduced, the |BoolExpr n| is evaluated under this
environment.


\begin{shade}
\begin{code}
proofGoal      :    (n m : ℕ) → Diff n m → BoolExpr m → Env n → Set
proofGoal           .m     m    (Base    ) b acc = P ⟦ acc ⊢ b ⟧ 
proofGoal           n      m    (Step y  ) b acc =
               (a : Bool) → proofGoal (1 + n) m y b (a ∷ acc)
\end{code}
\end{shade}


Now that we can interpret a |BoolExpr n| as a theorem using |proofGoal|, and we have a
way to decide if something is true for a given environment, we 
need to show the soundness of our decision function |foralls|. That is, we need
to be able to show that a formula is true if it holds for every
possible assignment of its variables to |true| or |false|. 

This is done in the function |soundness|, of which we only provide the
type signature. It requires the predicate |foralls| which is only
satisfied when a proposition is a tautology, and gives back a proof
which has the type computed by |proofGoal|. It uses the predicate to
safely extract the leaf from |foralls| corresponding to any given
environment resulting from the binders introduced by |proofGoal|.

\begin{shade}
\begin{code}
soundness       : {n : ℕ}    → (b : BoolExpr n) → {p : foralls b}
                             → proofGoal' 0 n (zero-least 0 n) b []
\end{code}%
\ignore{%
\begin{code}
soundness {n} b {p}          = soundnessAcc b [] (zero-least 0 n) p
\end{code}%
}%
\end{shade}

Now, we can prove theorems by a call of the form |soundness b {p}|, where |b| is the
representation of the formula under consideration, and |p| is the evidence
that all branches of the proof tree are true.
We do not give |p| explicitly since the only valid values are
nested pairs of |tt|, which can be inferred automatically. % for closed
% terms if the type is inhabited.  
This once again exploits the fact
that Agda supports eta expansion for record types.

If the module
type checks, we know that the representation of the formula corresponds to the concrete
expression, |soundness| gave a valid proof, and that the formula is in fact a tautology.
We also have the corresponding proof object at our disposal,
as in  |someTauto| (Fig.~\ref{fig:dup}).

\begin{shadedfigure}[b]
\begin{code}
rep          : BoolExpr 2
rep          = Imp    (And (Atomic (Fsuc Fzero)) (Atomic Fzero)) 
                      (Atomic Fzero)

someTauto    : (p q : Bool)         → P( p ∧ q ⇒ q )
someTauto    = soundness rep
\end{code}
\caption{An example Boolean formula, along with the transliteration to a proposition and the corresponding proof.}\label{fig:dup}
\end{shadedfigure}

If one were to give as input a formula which is not a tautology, Agda would not be able to infer the proof |foralls|, since
it would be an uninhabited type. As before, this would result in an unsolved meta-variable (a type error stating |Error| and |⊤| cannot be unified).
Agda disallows
importing modules with unsolved meta-variables, which means such an unfulfilled proof obligation would not be usable elsewhere
in a real-life development. 

\paragraph{Limitations.}\label{para:limi} Unfortunately, this approach is only possible using variables with a finite type. If we wanted
to prove properties about naturals, for example, we would not be able to enumerate all possible values.
Also, not all problems are decidable. In the ring solver
example~\cite{ringsolver} a canonical representation is used, but this
does not always exist. One way forward would be if a proof search
system could be implemented, going beyond simple reflection. By
inspecting the shape of the obligation it might be possible to find a
lemma which sufficiently reduces the goal to something we can easily
generate.  This is motivated by the evenness example: we could imagine
it being possible to automatically prove lemmas like |Even n -> Even
(n + 100)|, given a list of usable lemmas. On inspecting the goal and
finding the |Plus (Var n) 100| term, we might be able to learn that
this lemma (which would have a particularly tedious proof) is an
instance of |Even x -> Even y -> Even (x + y)|, which might be an
existing library proof. However, this would require a rather advanced
way of recognising structures in proof goals, and a reliable proof
search for useful lemmas in a database. 
This would correspond to implementing an analogue of Coq's \texttt{auto} tactic
in Agda. The Agda synthesizer Agsy already implements such a  proof search,
but is built directly into the compiler.
 This is definitely an avenue for future
work.



\paragraph{Summary.} The only thing we still have to do manually is convert the 
Agda representation of the formula (|p ∧ q ⇒ q|, for example) into our abstract
syntax (|rep|). This is unfortunate, as we end up typing out the
formula twice. We also have to count the number of variables
ourselves and convert them to De Bruijn indices. This is
error-prone given how cluttered the abstract representation can get
for formulae containing many variables. 

We would like this transliteration
process to be automated. Luckily |Autoquote| is available
for precisely this purpose, and we show this now.


\subsection{Adding Reflection}\label{sec:addrefl}

It might come as a surprise that in a paper focusing on reflection --
in the programming language technology sense -- we have not yet
presented a convincing use for reflection. 
We can get rid of the duplication seen in Fig.~\ref{fig:dup} using Agda's reflection API. 
% There we see the same Boolean formula twice: once in the type signature as an Agda
% proposition and once expressed as a  |BoolExpr|. 
Using
the |quoteGoal| keyword to inspect the
current goal would give us the Agda representation, and passing that to |Autoquote|, 
 we can
convert it to its corresponding |BoolExpr|.


The conversion between a |Term| and |BoolExpr| is achieved in two phases, necessary
because
|Autoquote| only supports non-dependent data types, and
|BoolExpr n| has an argument of type |Fin n| to its constructor |Atomic| (see Fig.~\ref{fig:boolexprn}).
To work around this, we introduce a simpler, intermediary data structure, to which we will convert
from |Term|. This type, called |BoolInter|, is not shown here, but the only difference with |BoolExpr n| is that its
variables are represented by |Nat|s instead of |Fin|s.

The |Autoquote| library uses a lookup table, mentioning which constructor represents
variables and how names map to constructors. This way
only |Term|s containing variables or the usual operators 
are accepted. Using the mapping presented in Fig.~\ref{fig:booltable}, we can
construct a function that, for suitable |Term|s,
gives us a value in |BoolInter|. 

\begin{shadedfigure}
\begin{code}
boolTable : Table BoolInter
boolTable = (Atomic ,   (quote _∧_      )   ↦ And                 ∷     (quote _∨_      )      ↦ Or
                  ∷     (quote  ¬_      )   ↦ Not                 ∷     (quote true     )      ↦ Truth
                  ∷     (quote false    )   ↦ Falsehood           ∷     (quote _⇒_      )      ↦ Imp           ∷ [])
\end{code}
\caption{The mapping table for quoting to |BoolInter|.}\label{fig:booltable}
\end{shadedfigure}

Once we have a |BoolInter| expression, the second phase is to check that its
variables are all in scope (this means that $\forall$ |Atomic| $x  :     x < n$, if we
want to convert to a |BoolExpr n|), and replace all |ℕ| values with their |Fin n| counterparts.
We can now write a function |proveTautology|, which uses the automatic quoter and calls |soundness| on the resulting term. An
approximation of |proveTautology|'s type is given here. In summary, it
takes a term (as bound in the body of |quoteGoal|), quotes it with
|Autoquote|, passes it to |soundness|, which returns a term 
fulfilling the |proofGoal| type.


\begin{shade}
\begin{spec}
proveTautology : (t : Term) →      let      t' = doConvert boolTable t
                                   in ...   {i : foralls t'} →                     proofGoal n t'
\end{spec}
\end{shade}

That is all we need to automatically prove that
formulae are tautologies.  The following snippet illustrates the use of
the |proveTautology| function; we can omit all arguments except |e|, since they
  can  be inferred.

\begin{shade}
\begin{code}
peirce     :    (p q : Bool) → P(((p ⇒ q) ⇒ p) ⇒ p)
peirce     =    quoteGoal e in proveTautology e
\end{code}
\end{shade}

With that, we have automatically converted propositions in Agda to our
own AST, generated a proof of their soundness, and converted that back into a proof term
for the concrete formula. 

\section{Discussion}\label{sec:discussion}

 
\paragraph{Related Work.}  %
Our main innovations are novel combinations of existing
techniques. As a result, quite a number of subjects are relevant to mention
here.
 
As far as reflection in general goes, Demers and Malenfant~\cite{demers1995reflection} provide an informative historical overview.
What we are referring to as reflection dates back to work by Smith~\cite{Smith:1984:RSL:800017.800513}
and was initially presented in Lisp in the 80s. Since then,
many developments in the functional, logic as well as object-oriented programming worlds have 
emerged -- systems with varying power and scope \citep{DBLP:journals/lisp/Stump09}, \citep{Goldberg:1983:SLI:273}.
Unfortunately, reflection
is often unsafe: in Smalltalk and Objective-C, for example, calling
non-existent functions causes exceptions, to name just one pitfall.

These systems have inspired the reflection mechanism introduced
in Agda, which is lacking in a number of fundamental
capabilities -- most notably type awareness of |unquote|, type preservation
when using |quoteTerm| and inability to introduce top-level definitions. 
Nevertheless, it does provide the safety of a strong type system.

\paragraph{Evaluation.} %
If we look at the taxonomy of reflective systems in programming language technology written up 
by Sheard~\cite{sheard-staged-programming},
we see that we can make a few rough judgements about the metaprogramming facilities Agda currently 
supports.\footnote{Of course, having been implemented during a single
Agda Implementors' Meeting~\cite{thorsten-communication}, the current
implementation is more a proof-of-concept, and is still far from
being considered finished, so it would be unfair to judge the current implementation all too harshly. In
fact, we hope that this work might motivate the Agda developers to include some more features, to
make the system truly useful. }
 
\begin{itemize}
\item Agda's current reflection API leans more towards analysis than generation,
\item it supports encoding of terms in an algebraic data type (as opposed to a string, for example),
\item it involves manual staging annotations (by using keywords such as |quote| and |unquote|),
\item it is homogeneous, because the object language is the
  metalanguage. The object language's representation is a native
  data type.
\item It is only two-stage: we cannot as yet produce an object program which is itself a metaprogram. This is
  because we rely on  keywords such as |quote|, which cannot be represented.
\end{itemize}
 
 
As far as the proof techniques used in Sec.~\ref{sec:proof-by-reflection} are concerned,  
Chlipala's work~\cite{chlipala2011certified} proved an invaluable resource. One motivating example
for doing this in Agda was Jedynak's ring solver~\cite{ringsolver}, which is the first example of Agda's reflection
API in use that came to our attention. Compared to Jedynak's work, the proof generator presented here is marginally more refined in terms of the interface
presented to the user. We expect that approaches of this kind will become commonplace for proving mundane lemmas in 
large proofs. The comparison to tactics in a language like Coq is a tempting one, and we see both advantages and disadvantages of each style. Of course, 
the tactic language in Coq is much more specialised and sophisticated, but it is a pity that it is separate.
This paper explores an alternative, with metaprograms written directly in the object language. Some people might also appreciate
the 
fact that proof generation in Agda is explicit. 

Performance is another possible area of improvement. Introducing reflective proofs requires a lot of compile time computation,
and for this approach to scale, Agda would need a more efficient static evaluator  than the current call-by-name
implementation. 
The extensive use of proof
by reflection in Coq and SSReflect~\cite{gonthier:inria-00515548}, for example for proving the four colour theorem~\cite{DBLP:conf/ascm/Gonthier07}, has
motivated a lot of recent work on improving Coq's compile time
evaluation. We hope that Agda will be similarly improved.
 
\paragraph{Conclusions.} %
Returning to our research question,  repeated here,
a summary of findings is made.

\researchquestion

This paper
shows that the reflection capabilities recently added to Agda are
quite useful for automating tedious tasks.  
For example, we now need
not encode expressions manually: using |quoteTerm| and |Autoquote|,
some AST conversion can be done automatically.  
Furthermore, by using
the proof by reflection technique, we have shown how to automatically
generate a simple class of proofs, without loss of general applicability. 
Constraining
ourselves to (pairs of) unit types as predicates, we can let Agda
infer them, and by tagging an empty type with a string, we can achieve
more helpful errors if these predicates are invalid. These simple
tools were sufficient to engineer relatively powerful and -- more
importantly -- easily usable proof tools. Unfortunately, these proofs are limited
to finite domains, and are still not very scalable or straightforward to implement. In particular, quantifying
over variables with infinite domains should not be a great conceptual difficulty, but would necessitate
a lot of extra machinery: a smarter goal inspector, and a generalised lemma searching or matching algorithm.
Simple pattern matching on |Name|s would also be a useful feature.

It seems conceivable that in the future, using techniques such as those presented
here, a framework for tactics might be within reach. Eventually we might be able to define an
embedded language in Agda, in the style of Coq's tactic language, then
inspect the shape of the proof obligation, and look at a database
of predefined proof recipes to see if one of them might discharge or simplify the obligation. An advantage of 
this approach versus the tactic language in Coq, would be that the language of the propositions and
tactics is the same.

\subsubsection{Acknowledgements.} %
We would like to thank each of the four anonymous reviewers for taking
the time to provide detailed and constructive comments that greatly
improved the article.

\bibliography{refs}{}
% for LNCS bibliography:
\bibliographystyle{splncs}
\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-parse-self: t
%%% TeX-master: t
%%% TeX-command-default: "lagda2pdf"
%%% End: 
