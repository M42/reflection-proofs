%\documentclass[a4paper]{report}
\documentclass[a4paper]{llncs}

\usepackage{color}
\usepackage[usenames,dvipsnames,svgnames,table]{xcolor}
\usepackage{todonotes}

%include polycode.fmt
%if style == newcode
%else
%include agda.fmt
%include generated-colour.fmt
%include codecolour.fmt
%endif


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% stuff only for DRAFT versions
%%%%% microtype with settings.
%\usepackage[activate={true,nocompatibility},final,tracking=true,kerning=true,spacing=true,factor=1100,stretch=10,shrink=10]{microtype}
%\microtypecontext{spacing=nonfrench}
\newcommand{\microtypesetup}[1]{\fbox{NO MICROTYPE!\phantom{\rule{0.1\textwidth}{0.1\textwidth}}}}

\usepackage{draftwatermark}
\SetWatermarkLightness{0.95}
%% end DRAFT-version stuff.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage{subfigure}
\usepackage{xspace}
\usepackage{textcomp} % text-mode <> characters


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% Font definitions.
\usepackage{tgpagella}                  %% looks a little like palatino -- thanks Zapf!
\usepackage[T1]{fontenc}
\renewcommand{\ttdefault}{lmtt}         %% Latin Modern for teletype
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcommand{\ignore}[1]{}

\newcommand{\pref}[1]{~\ref{#1} on page~\pageref{#1}}

% brace yourself!
\newcommand{\bracket}[1]{{[}#1{]}}

\newcommand{\ghloc}{https://github.com/toothbrush/reflection-proofs}
\newcommand{\ghurl}{\url{\ghloc}}
\def\CC{{C\nolinebreak[4]\hspace{ -.05em}\raisebox{.2ex}{\small\bf ++}}}
\colorlet{hlite}{CornflowerBlue!15!white}

\newcommand{\hlitem}[1]{\item[\colorbox{hlite}{#1}]~\\}
\newcommand{\ch}{Curry--Howard isomorphism\xspace}
% This defines figures with backgrounds -- useful for code
\usepackage{adjustbox}
\usepackage{float} % enable H position specifier
% \newenvironment{shadedfigure}{\begin{figure}}{\end{figure}}
% \newenvironment{shade}{}{}
\newenvironment{shadedfigure}[1][tbhp]{%
    \begin{figure}[#1]
    \begin{adjustbox}{minipage=\linewidth-10pt,margin=5pt,bgcolor=hlite}
}{%
    \end{adjustbox}
    \end{figure}
}
\newenvironment{shade}{

\vskip 0.5\baselineskip
\begin{adjustbox}{%
minipage=\linewidth,margin=0pt,padding=0pt,bgcolor=hlite%
}}{%
\end{adjustbox}
\vskip 0.5\baselineskip

}

\newcommand{\lagda}{\texttt{\--\--{}lagda}\xspace}
\ignore{
\begin{code}
module doc.ReflectionProofs where

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
open import Data.Fin hiding (_+_)


\end{code}
}

\usepackage{amsmath}

%%%% the semantic package, for the nice type rules.
%\usepackage{semantic}
%\mathlig{ ->}{ \to}
%\mathlig{||->}{\mapsto}
%\mathlig{||=>}{\Mapsto}
%\mathlig{=>}{\Rightarrow}
%\mathlig{||- }{\vdash }
%\mathlig{~>}{\leadsto}
%\mathlig{=/=}{\neq}
%%%% end semantic package stuff.

\usepackage{hyperref}
\usepackage{url}

%% Give citations etc a nicer look
\hypersetup{
  colorlinks,
  citecolor=DarkBlue,
  linkcolor=black,
  urlcolor=DarkBlue}
  
\date{\today}
\newcommand{\HRule}{\noindent\rule{\linewidth}{1.5pt}}
\title{Engineering Proof by Reflection in Agda}
\author{Paul van der Walt \and Wouter Swierstra}
\institute{
\href{mailto:paul@@denknerd.org}{\nolinkurl{paul@@denknerd.org}}, \href{mailto:W.S.Swierstra@@uu.nl}{\nolinkurl{W.S.Swierstra@@uu.nl}}\\
Department of Computer Science, Utrecht University
}



\begin{document}

\maketitle

\begin{abstract}
  Detailing the implementation of proof by reflection using Agda's
  recent reflection API.
% This project explores the recent addition to Agda enabling
% \emph{reflection}, in the style of Lisp, MetaML, and Template
% Haskell. It illustrates several possible applications of reflection that arise
% in dependently typed programming, and details the limitations of the
% current implementation of reflection. Examples of type-safe metaprograms
% are given that illustrate the power of reflection coupled with a dependently 
% typed language. Among other things the
% limitations inherent in having |quote| and |unquote| implemented as
% keywords are highlighted. The fact that lambda terms are returned without
% typing information is discussed, and a solution is presented. Also
% provided is a detailed users' guide to the reflection API and a
% library of working code examples to illustrate how various common
% tasks can be performed, along with suggestions for an updated
% reflection API in a future version of Agda.
\end{abstract}



\newcommand{\researchquestion}{%
\begin{quote}
  ``What practical issues do we run into when trying to engineer
  automatic proofs in a dependently typed language with reflection?
  Are Agda's reflective capabilities sufficient and practically
  usable, and if not, which improvements might make life easier?''
\end{quote}
}

\section{Introduction}\label{chap:introduction}

Since the inception of computer programming, one of the aims has been to
try and write as little code as possible, while achieving the most powerful effect.
One of the holy grails of writing programs is also being able to reuse pieces of
code, after having written them once, as opposed to continually writing small
variations on existing code. Reinventing the wheel is something the programmer
should not relish doing.

One of the many techniques for writing more effective
code is that of \emph{metaprogramming}, which refers
to the ability of a program to inspect\footnote{or \emph{reflect} upon} its own code,
possibly modifying it. This has long been a favourite
feature of users of such languages as Lisp~\cite{lisp-macros}. In many cases, this allows
code to be a lot more concise and general, and thus reusable, than 
usually is possible in simple imperative languages.

The dependently typed programming language
Agda~\cite{norell:thesis,Norell:2009:DTP:1481861.1481862} has recently been
extended with a \emph{reflection mechanism} for compile time metaprogramming in the style of Lisp~\cite{lisp-macros},
MetaML~\cite{metaml}, Template Haskell~\cite{template-haskell}, and
\CC\ templates~\cite{cplusplus}. Agda's reflection mechanisms make it
possible to convert a program fragment into its corresponding abstract
syntax tree (AST) and vice versa. In tandem with Agda's dependent types,
this has promising new programming potential.


The main questions we aim to answer during this project are:


\researchquestion



\paragraph{Contributions} This project starts to explore the possibilities and limitations of this
new reflection mechanism. It describes a case study,
exemplative of the kind of problems that can be solved using
reflection. More specifically it makes the following contributions:

\begin{itemize}
  \item A newcomers' crash course on reflection in Agda is given in Sec.~\ref{sec:crash}.
\item A library called |Autoquote| is presented, which alleviates much
  of a programmer's burden when quoting a given AST. The
  library is introduced in Sec.~\ref{sec:introducing-autoquote}.
\item How to use Agda's reflection mechanism to
  automate certain categories of proofs is illustrated in
  Sec.~\ref{sec:proof-by-reflection}. The idea of \emph{proof by
    reflection} is certainly not new, but still worth examining in the
  context of this new technology.
\end{itemize}

The code and examples presented in this paper all compile using the
latest version of Agda (currently 2.3.2). All code, including this
report, is available on
GitHub\footnote{\ghurl}.
This report is also a Literate Agda file, which means the code snippets can be extracted, compiled 
and played around with.



\subsection{Introducing Agda}\label{sec:reflection}

The programming language Agda is an implementation
of Martin-L\"of's type theory \cite{Martin-Lof:1985:CMC:3721.3731}, extended with records and modules. Agda
is developed at the Chalmers University of Technology
\cite{norell:thesis}; thanks to the \ch, it is
both a 
functional programming language
and a proof assistant for intuitionistic logic. It is comparable with
Coquand's calculus of constructions, the logic behind Coq \cite{DBLP:journals/iandc/CoquandH88}. Coq is
similarly both a programming language and proof assistant.

For an excellent tutorial on dependently typed programming using Agda,
the reader is referred to Norell's work \cite{Norell:2009:DTP:1481861.1481862}.

Before diving into the details of proof by reflection, Sec. \ref{sec:thebasics}
provides a crash course
on Agda's
recent reflection API. 



Since version 2.2.8, Agda includes a reflection API \cite{agda-relnotes-228}, which allows converting
parts of a program's code into abstract syntax, in other words a data structure
in Agda itself, that can be inspected or modified like any other data structure.
The idea of reflection is old: already in the 1980s Lisp included a similar
feature, called \emph{quoting} and \emph{unquoting}, which allowed run time modification of a program's code, by
the program itself. This has given rise to powerful techniques for reusing code and
generating frequently needed but slightly different expressions automatically. What
can be done with Lisp, can be done better using dependent types; at least, so we hope. This chapter
looks at 
how to use reflection in Agda. It should be a good starting point for someone already comfortable with
Agda, or at the very least dependent types, to find inspiration on how to make reflection work to their advantage.

Agda's reflection API defines several data types which represent terms,
types, and sorts. These definitions take into account various Agda-specific
features, including hidden arguments and computationally irrelevant
terms. 
In addition to these data
types that represent \emph{terms}, there is limited support for
reflecting \emph{definitions}, although we will not use this capability.

\section{Using Reflection}\label{sec:crash}

Before going into too much detail about how reflection can make our
lives easier and what nifty techniques are possible, we will look at a few simple code snippets which should serve
to illustrate the basics of using the reflection API in Agda.



\paragraph{The Keywords} There are several new keywords that can be used to quote and unquote
|Term| values: |quote|, |quoteTerm|, |quoteGoal|, and |unquote|. The
|quote| keyword allows the user to access the internal representation of
any identifier, or name. This internal representation can be used to query the
type or definition of the identifier.


The easiest example of quotation uses the |quoteTerm| keyword to turn
a fragment of concrete syntax into a |Term| value. Note that the
|quoteTerm| keyword reduces like any other function in Agda. As an
example, the following unit test type checks:

\begin{shade}
\begin{code}
example₀   : quoteTerm (\ (x : Bool) -> x)
           ≡ lam visible (var 0 [])
example₀   = refl
\end{code}
\end{shade}

Dissecting
this, we introduced a lambda abstraction, so we expect the |lam|
constructor. Its one argument is visible, and
the body of the lambda abstraction is just a reference to the
nearest-bound variable, thus |var 0|, applied to an empty list of arguments.

Furthermore, |quoteTerm| type checks and normalises its term before
returning the required |Term|, as the following example demonstrates:
\begin{shade}
\begin{code}
example₁   : quoteTerm ((\ x → x) 0) ≡ con (quote ℕ.zero) []
example₁   = refl
\end{code}
\end{shade}

See how the zero is applied to the identity function, resulting in only the value zero.
The quoted representation of a natural zero is |con (quote zero) []|, where |con| means that we
are introducing a constructor. The constructor |zero| takes no arguments, hence the empty list.

The |quoteGoal| keyword is slightly different. It is best explained using an
example:

\begin{shade}
\begin{spec}
exampleQuoteGoal : ℕ
exampleQuoteGoal = quoteGoal e in (HOLE 0)
\end{spec}
\end{shade}

The |quoteGoal| keyword binds the variable |e| to the |Term|
representing the type of the current goal. In this example, the value
of |e| in the hole will be |def ℕ []|, i.e., the |Term| representing
the type |ℕ|.


The |unquote| keyword converts a |Term| data type back to concrete
syntax. Just as |quoteTerm| and |quoteGoal|, it type checks and
normalises the |Term| before it is spliced into the program text.



Finally, we have decidable equality on the following types: |Visibility|, |Relevance|, |List Arg|s, |Arg Type|s, |Arg Term|s,  |Name|s,  |Term|s, |Sort|s  and |Type|s. 
Typically, this is useful for deciding which constructor is present in
some expression, by comparing to known |Name|s. Such a comparison is illustrated in the function |convert|, below.

\begin{shade}
\begin{spec}
convert : Term → Something
convert (def c args) with c ≟-Name quote foo
...                   | yes p     = (HOLE 0) -- |foo| applied to arguments
...                   | no ¬p     = (HOLE 1) -- a function other than |foo|
\end{spec}
\end{shade}

This short introduction should already be enough to start developing
simple reflective programs.  For a more detailed description of the
reflection API in Agda, including many examples, the inquisitive
reader is referred to the more extensive thesis covering this topic \cite{vdWalt:Thesis:2012}.
The thesis goes into more detail
regarding the data structures involved in Agda's reflection API, and later, 
gives a detailed account of some real-world use-cases.



\section{Automatic Quoting}\label{sec:autoquote}
\ignore{
\begin{shade}
\begin{code}
open import Metaprogramming.Autoquote hiding (convertManages ; doConvert) renaming (_#_↦_ to _\#_↦_)
\end{code}
\end{shade}
}

In a language like Haskell, which has pattern matching, converting
elements of one AST to another is usually a simple, if boring,
task. Unfortunately for us, though, Agda functions are required to be
total, having cases for each possible pattern. Since the AST of terms
which can be quoted is usually much more liberal than an AST we would
like to use (such as that of Boolean expressions, or first-order
equations, for example), writing such conversion functions can be tedious.

%TODO ease the transition here...
If, each time we wanted to quote a term, we had to write a huge function, with many pattern matching cases and nested |with| statements to handle different 
shapes of ASTs, we would quickly become discouraged. This nearly happened while doing this project, which is why
|Autoquote| was conceived. Quoting some expression with a given grammar is a mundane task we are frequently faced with if we 
are foolhardy enough to use reflection. The (partial) solution to this problem~-- something which at least mitigates 
the agony~-- is presented in this section.

Imagine we have some AST, for example |Expr|, as in Fig.~\ref{fig:exprdata}.
This is a rather simple inductive data structure representing terms which can contain Peano style natural
numbers, variables (indexed by an Agda natural) and additions.

\begin{shadedfigure}[h]
\begin{code}
data Expr : Set where
  Var           : ℕ               →     Expr
  Pl            : Expr → Expr     →     Expr
  S             : Expr            →     Expr
  Z             :                       Expr
\end{code}
\caption{The toy expression language |Expr|. We would like support for automatically quoting such terms.}\label{fig:exprdata}
\end{shadedfigure}

We might conceivably want to convert a piece of Agda concrete syntax, such as $5 + x$, to this
AST, using reflection. This typically involves ugly and verbose functions like
the one from Sec.~\ref{sec:Boolean-tautologies} with many |with| clauses and frankly, too
much tedium to be anything to be proud of. 
%%%%%%%%%%%%%%%
\begin{shadedfigure}[h]
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
\caption{The gist of  the conversion of a |Term| into a |BoolExpr n|.}\label{fig:concrete2abstract}
\end{shadedfigure}
%%% an example conversion function which is fugly
%%%%%%%%%%%%%%%

We need to check that the |Term| has a reasonable shape, and contains valid operators.
Ideally, we would 
 provide a mapping from concrete constructs such as the |_+_| function to elements of our
AST, and get a conversion function for free.
 This motivated my development of
|Autoquote| in the course of this project. What |Autoquote| does is abstract over this process, and
provide an interface which, when provided with such a mapping, automatically quotes expressions
that fit. Here, \emph{fitting} is defined as only having variables, or names that are listed
in this mapping. Other terms are rejected.
The user provides an elegant-looking mapping and |Autoquote| automatically converts
concrete Agda to elements of simple inductive types. The mapping table for |Expr| is
shown in Fig.~\ref{fig:exprTable}.

\begin{shadedfigure}[h]
\begin{code}
exprTable : Table Expr
exprTable = (Var ,
             2   \# (quote _+_)      ↦ Pl   ∷
             0   \# (quote ℕ.zero)   ↦ Z    ∷
             1   \# (quote ℕ.suc)    ↦ S    ∷ [])
\end{code}
\caption{The mapping table for converting to the imaginary |Expr| AST. }\label{fig:exprTable}
\end{shadedfigure}

How this should be interpreted is that any variables encountered should be stored as |Var|s, and
the |_+_| operator should be a |Pl| constructor. In each case we are required to manually specify the
arity of the constructor:    how many arguments it expects.
A |zero|, from the |Data.Nat| standard library, should be treated as our |Z| constructor, and
a |suc| translates to |S|. These constructors expect 0 and 1 argument, respectively.

We will now look at the implementation of this library.

\paragraph{Implementation} %TODO should we talk about this so much?
% no change to Usage and afterwards have a VERY BRIEF Implementation
% paragraph which explains in words what's happening.



\begin{shade}
\begin{code}
convertManages : {a : Set} → Table a → Term → Set
convertManages t term with convert t term
convertManages t term | just x       = ⊤
convertManages t term | nothing      = ⊥

doConvert : {a : Set}      → (tab : Table a) 
                           → (t : Term) 
                           → {man : convertManages tab t} 
                           → a
doConvert tab t {man   }      with convert tab t
doConvert tab t {man   }      | just x     = x
doConvert tab t {()    }      | nothing
\end{code}
\end{shade}

The use of |convertManages| and |doConvert| is illustrated in Fig.~\ref{fig:test-autoquote}. 
This approach, using |convertManages| as an assumption, is a lot simpler than writing by hand a predicate function with the same pattern matching 
structure as |convert|. Adding to the complication, |with| clauses are often expanded unpredictably in practise. The net effect
of writing a pair of functions in this style is the same as the ``usual'' way of writing a predicate
function by hand, in that a compile time error is generated if the function |doConvert| is 
invoked on an argument with the wrong shape. Compare these relatively elegant functions to the verbose |term2boolexpr| and |isBoolExprQ| functions in Sec.~\ref{sec:addrefl}.


\begin{shadedfigure}[h]
\begin{code}
something : {x y : ℕ}    → doConvert    exprTable
                                        (quoteTerm ((1 + x + 2) + y))
                         ≡ S    (Pl         (Pl       (Var 1)
                                                      (S (S Z)))
                                            (Var 0))
something = refl
\end{code}
\caption{An example of |Autoquote| in use. See Fig.~\ref{fig:exprTable} for the definition of |exprTable|, a typical |Name|-to-constructor mapping.}\label{fig:test-autoquote}
\end{shadedfigure}


The format of the translation |Table| required could most probably be made a little simpler,
by not requiring the user to provide the arity of the function, but using the tools 
explained in Sec.~\ref{sec:inspecting-definitions} (the section on inspecting data definitions,
and specifically the function |constructors| in combination with |type|) to try and discover the arity of the various constructors.
Because of time constraints, however, this is left as a suggestion for future work on the |Autoquote| library.

The |BoolExpr| AST used later in Sec.~\ref{sec:Boolean-tautologies} provides a
good motivating example for using |Autoquote|, therefore a slightly
more real-world example of |Autoquote| in use can be found in
Sec.~\ref{sec:autoquote-example}. One might also use the ability of quoting 
arithmetic equations shown here in combination with a monoid solver,
such as the example in Norell \emph{et al.} \cite{bove2009brief}.

Further examples of |Autoquote| functionality can be found in the module |Metaprogramming.ExampleAutoquote|.
The module |Metaprogramming.Autoquote| contains 
what could serve as a basis for a system for quoting concrete Agda into a more complex user-defined AST.
Now that we have had a quick introduction to Agda in Sec.~\ref{chap:introducing-agda}, and defined
this library, it is time to move on to putting it all to use.


\section{Proof by Reflection}\label{sec:proof-by-reflection}

The idea behind proof by reflection is simple: given that type theory
is both a programming language and a proof system, it is possible to
define functions that compute proofs. Reflection is an overloaded word
in this context, since in programming language technology reflection
is the capability of converting some piece of concrete code
into an abstract syntax tree object that can be manipulated in the same
system. Reflection in the proof technical sense is the method of
mechanically constructing a proof of a theorem by inspecting its
shape.
Here we will see two case studies illustrating proof by
reflection and how Agda's reflection mechanism can make the technique
more convenient.



\subsection{Simple Example: Evenness}\label{sec:evenness}

Sometimes, the best way to explain a complicated topic is to start by giving 
some simple examples, letting the reader figure out the pattern behind what is being
done themselves. Proof by reflection is no different: it is not a difficult technique, but can initially be
counter intuitive. 

To illustrate the concept of proof by reflection, we will cover an example taken from
Chlipala~\cite{chlipala2011certified}, where a procedure is developed to automatically
prove that a number is even. We start by defining the
property |Even| below. There are two constructors: the first
constructor says that zero is even; the second constructor states that
if $n$ is even, then so is $2 + n$.

\begin{shade}
\begin{code}
data Even      : ℕ → Set where
  isEven0      :                          Even 0
  isEven+2     : {n : ℕ} → Even n     →   Even (2 + n)
\end{code}
\end{shade}

Using these rules to produce the proof that some large number $n$ is
even is tedious: the proof that $2 \times n$ is even requires $n$
applications of the |isEven+2| constructor. For example, here is the
proof that 6 is even:

\begin{shade}
\begin{code}
isEven6 : Even 6
isEven6 = isEven+2 (isEven+2 (isEven+2 isEven0))
\end{code}
\end{shade}

To automate this, we will show how to \emph{compute} the proof
required. We start by defining a predicate |even?| that
returns the unit type when its input is even and bottom otherwise.
In this context, |⊤| and |⊥| can be seen as the analogues of |true|
and |false|, just as presented in Sec.~\ref{sec:plandpa}.
The meaning of such a decision function is that there exists
a proof that some number is even, if it is $0$ or $2 + n$, for even $n$. Otherwise, no proof exists. That is the
claim, at least. The idea
of ``there exists'' is perfectly modelled by the unit and empty types,
since the unit type has one inhabitant, the empty type none.

\begin{shade}
\begin{code}
even? : ℕ → Set
even? 0                 = ⊤
even? 1                 = ⊥
even? (suc (suc n))     = even? n
\end{code}
\end{shade}


Next we need to show that the |even?| function is \emph{sound}; that
our claim holds. To do so, we prove that when |even? n| returns |⊤|,
the type |Even n| is
inhabited, and since we are working in a constructive logic, the only
way to show this is to give some witness. This is done in the function |soundnessEven|. What
we are 
actually doing here is giving a recipe for
constructing proof trees, such as the one we manually defined for
|isEven6|.

\begin{shade}
\begin{code}
soundnessEven : {n : ℕ} → even? n → Even n
soundnessEven {0}              tt        = isEven0
soundnessEven {1}              ()
soundnessEven {suc (suc n)}    s         = isEven+2 (soundnessEven s)
\end{code}
\end{shade}

Note that in the case branch for 1, we do not need to provide a
right-hand side of the function definition. The assumption, |even?
1|, is uninhabited, and we discharge this branch using Agda's
absurd pattern, \texttt{()}.

Now that this has been done, if we need a proof that some arbitrary
|n| is even, we only need to call |soundnessEven|. Note that
the value of |n| is an implicit argument to |soundnessEven|. The only
argument we need to provide to our |soundnessEven| lemma is a proof
that |even? n| is inhabited. For any closed term, such as the numbers |28|
or |8772|, this proof obligation reduces to 
|⊤|, which is proven by the single constructor it has, |tt|.

\begin{shade}
\begin{code}
isEven28        : Even 28
isEven28        = soundnessEven tt

isEven8772      : Even 8772
isEven8772      = soundnessEven tt
\end{code}
\end{shade}

Now we can easily get a proof that arbitrarily large numbers are even,
without having to explicitly write down a large proof tree. Note that
it is not possible to write something with type |Even 27|, or any other uneven
number, since the parameter |even? n|  is equal to |⊥|,
 thus
|tt| would not be accepted where it is in the |Even 28| example. This will
produce a |⊤ !=< ⊥| type error at compile time.
Note that it is possible to generate a user-friendly ``error'' of sorts, by replacing the |⊥| constructor in |even?| with
a type with a descriptive name such as @NotEven@. Of course it should still be an empty type, but possibly parameterised with a natural to
indicate which value is odd. This makes the soundness proof a little less straightforward, but in return the
type error generated if an odd number is used becomes more informative. This enhancement is demonstrated in Fig.~\ref{fig:error}, in the Boolean
tautologies example.

Since the type |⊤| is a simple record type, Agda can infer the |tt|
argument, as explained in Sec.~\ref{sec:implicit-unit}. This means we can turn the assumption |even? n| into an
implicit argument, so a user could get away with writing just
|soundnessEven| as the proof, letting the inferrer do the rest. For
the sake of exposition this is not done here, but the final implementation
available on GitHub does use this trick. A detailed explanation of this
technique, which is used extensively in the final code, is given in
Sec.~\ref{sec:implicit-unit}.  Note that it still has the minor danger of
making errors look like innocuous warnings.

%TODO implement trick here.

This concludes the example of proving that certain naturals are even using proof by reflection.
The next step will be to use the same approach for a more involved and realistic problem.

\subsection{Second Example: Boolean Tautologies}\label{sec:Boolean-tautologies}

Obviously, the first example of proof by reflection, the evenness of natural 
numbers, was a rather trivial one. There was a good reason for studying it, though, since
we will now apply the same technique to a more interesting problem, making
the relationship to the previous example clear at each step.

Another application of proof by reflection 
is Boolean expressions which are a tautology. We will prove this by evaluation of the
formulae. We will follow the same
recipe as for even naturals, with one further addition. In the
previous example, the input of our decision procedure |even?| and the
problem domain were both natural numbers. As we shall see, this need
not always be the case: more complex structures and properties may be used.

Take as an example the Boolean formula in equation \ref{eqn:tauto-example}.
\begin{align}\label{eqn:tauto-example}
(p_1 \vee q_1) \wedge (p_2 \vee q_2) \Rightarrow (q_1 \vee p_1) \wedge (q_2 \vee p_2)
\end{align}

It is trivial to see that this is a tautology, but proving this 
using deduction rules for classical logic would be rather tedious. It
is even worse if we want to check if the formula always holds by
trying all possible variable assignments, since this will give $2^n$
cases, where $n$ is the number of variables.

To automate this process, we will follow a similar approach to
the one given in the section on even natural numbers (Sec.~\ref{sec:evenness}). We start by defining an
inductive data type to represent Boolean expressions with at most $n$ free
variables in Fig.~\ref{fig:boolexprn}.

\begin{shadedfigure}[h]
\begin{code}
data BoolExpr (n : ℕ) : Set where
  Truth         :                                  BoolExpr n
  Falsehood     :                                  BoolExpr n
  And           : BoolExpr n → BoolExpr n      →   BoolExpr n
  Or            : BoolExpr n → BoolExpr n      →   BoolExpr n
  Not           : BoolExpr n                   →   BoolExpr n
  Imp           : BoolExpr n → BoolExpr n      →   BoolExpr n
  Atomic        : Fin n                        →   BoolExpr n
\end{code}
\caption{Inductive definition of Boolean expressions with $n$ free variables.}\label{fig:boolexprn}
\end{shadedfigure}



There is nothing
surprising about this definition; we use the type |Fin n| to ensure
that variables (represented by |Atomic|) are always in scope. If we want to
evaluate the expression, however, we will need some way to map variables to values.
Enter |Env n|: it has fixed size |n| since a |BoolExpr n| has at most $n$ free variables.

\begin{shade}
\begin{code}
Env   : ℕ → Set
Env   = Vec Bool
\end{code}
\end{shade}

Now we can define a decision function, which tells us if a given
Boolean expression is true or not, under some assignment of variables. It does this by evaluating
the formula's % the apostrophe is bonafide.
 AST, filling in for |Atomic| values the concrete values which are
looked up in the environment. For example, |And| is converted to
the Boolean function |_∧_|, and its two arguments in turn are
recursively interpreted.

\ignore{
\begin{code}
open import Proofs.Util.Handy
\end{code}
}

\begin{shade}
\begin{code}
⟦_⊢_⟧ : ∀ {n : ℕ} (e : Env n) → BoolExpr n → Bool
⟦ env     ⊢ Truth           ⟧ = true
⟦ env     ⊢ Falsehood       ⟧ = false
⟦ env     ⊢ And   be   be₁  ⟧ =     ⟦ env ⊢ be ⟧     ∧      ⟦ env ⊢ be₁ ⟧
⟦ env     ⊢ Or    be   be₁  ⟧ =     ⟦ env ⊢ be ⟧     ∨      ⟦ env ⊢ be₁ ⟧
⟦ env     ⊢ Not   be        ⟧ = ¬   ⟦ env ⊢ be ⟧
⟦ env     ⊢ Imp   be   be₁  ⟧ =     ⟦ env ⊢ be ⟧     ⇒      ⟦ env ⊢ be₁ ⟧
⟦ env     ⊢ Atomic n        ⟧ = lookup n env
\end{code}
\end{shade}

Recall our decision function |even?| in the previous section. It returned
|⊤| if the proposition was valid, |⊥| otherwise. Looking at |⟦_⊢_⟧|, we see that
we should just translate |true| to the unit type and false to the empty type, to get
the analogue of the |even?| function.

We call this function |So|, the string parameter serving to give a clearer type error
to the user, if possible.


\begin{shadedfigure}[H]
\begin{code}
data Error (e : String) : Set where

So   : String → Bool → Set
So   _        true     = ⊤
So   err      false    = Error err

P    : Bool → Set
P    = So "Argument expression does not evaluate to true."
\end{code}
\caption{Helper type |Error|, enabling clearer type errors.}\label{fig:error}
\end{shadedfigure}


Now that we have these helper functions, it is easy to define what it
means to be a tautology. We quantify over a few Boolean variables, and
wrap the formula in our |P| decision function. If the resulting type is
inhabited, the argument to |P| is a tautology, i.e., for each
assignment of the free variables the entire equation still evaluates
to |true|. An example encoding of such a theorem is Fig.~\ref{fig:exampletheorem}~-- notice
how similar it looks to the version expressed in mathematical notation, in equation~\ref{eqn:tauto-example}.

One might wonder why propositions are not encoded in the slightly more 
intuitive propositional equality style, for example |(b : Bool) → b ∨ ¬ b ≡ true|, since
that notation more obviously reflects the meaning of ``being a tautology'', as opposed 
to one having to understand the |So| function; this is justified in Sec.~\ref{sec:no-propositional-equality}.

\begin{shadedfigure}[h]
\begin{code}
exampletheorem : Set
exampletheorem = (p₁ q₁ p₂ q₂ : Bool)   →
                 P  (         (p₁ ∨ q₁) ∧ (p₂ ∨ q₂) ⇒ (q₁ ∨ p₁) ∧ (q₂ ∨ p₂))
\end{code}
\caption{Encoding of an example tautology.}\label{fig:exampletheorem}
\end{shadedfigure}

Here a complication arises, though. We are quantifying over a list of Boolean values \emph{outside}
of the decision function |P|, so proving |P| to be sound will not suffice. We just defined an evaluation function |⟦_⊢_⟧|
to take an environment, an expression, and return a Boolean. In Fig.~\ref{fig:exampletheorem}, though,
we effectively quantified over all possible environments. We are going to need a way
to lift our decision function to arbitrary environments.



The way we do this is the function |foralls|, in Fig.~\ref{fig:forallsacc}. This function represents the real analogue
of |even?| in this situation: it returns a type which is only inhabited if the argument Boolean
expression is true under all variable assignments. This is done by generating a full binary tree
of |⊤| or |⊥| types, depending on the result of |⟦_⊢_⟧| under each assignment.
This corresponds precisely to the expression being a tautology if and only if the tree is inhabited.

The |Diff| argument is unfortunately needed to prove that |forallsAcc| will eventually produce a
tree with depth equal to the number of free variables in an expression. 

\ignore{
\begin{code}
open import Proofs.Util.Lemmas renaming (zero-least to zeroleast)
open import Proofs.Util.Types using (Diff; Base; Step)
\end{code}
}

\begin{shadedfigure}[h]
\begin{code}
forallsAcc : {n m : ℕ} → BoolExpr m → Env n → Diff n m → Set
forallsAcc b acc    (Base     ) = P ⟦ acc ⊢ b ⟧
forallsAcc b acc    (Step y   ) =
  forallsAcc b (true ∷ acc) y × forallsAcc b (false ∷ acc) y

foralls : {n : ℕ} → BoolExpr n → Set
foralls {n} b = forallsAcc b [] (zeroleast 0 n)
\end{code}
\caption{The function |foralls|, which decides if a proposition is a tautology. Compare to the |even?| function in Sec.~\ref{sec:evenness}.}\label{fig:forallsacc}
\end{shadedfigure}


\paragraph{What Is This |Diff| You Speak Of?}\label{sec:explain-diff}

We just saw that the |Diff| argument is necessary in some
of the recursive functions. Here, a short description of what it is
and why it is needed is given.

In Sec.~\ref{sec:Boolean-tautologies} the function |forallsAcc| (among others)
has a parameter of type |Diff n m|. Recalling the function's
definition from Fig.~\ref{fig:forallsacc}, note that there are two variables, $n$ and $m$, giving the current size of the environment
and the maximum number of bound variables in the proposition, respectively. 

This is wrong, since our interpretation function |⟦_⊢_⟧| requires that these $m$ and $n$ are equal.
We cannot, however, make them equal in the type signature for |proofGoal|, since we are 
recursively building up the environment with an accumulating parameter. Because of this, we introduce |Diff|~-- see Fig.~\ref{fig:diff-datatype}.


\begin{shadedfigure}[h]
\begin{spec}
data Diff' : ℕ → ℕ → Set where
  Base   : ∀ {n}                          → Diff' n n
  Step   : ∀ {n m} → Diff' (suc n) m      → Diff' n m
  
zeroleast : (k n : ℕ) → Diff k (k + n)
\end{spec}
\caption{The definition of the |Diff| data type.}\label{fig:diff-datatype}
\end{shadedfigure}

The |Diff| data type  was necessary because given a term of type |BoolExpr m|, being a
proposition with at most $m$ variables, it should be ensured that in
the end an environment of size $m$ would be produced.  The necessity
of $m \equiv n$ is obvious considering that the evaluation function
needs to be able to look up the variables in the Boolean expression.
As |forallsAcc| is a recursive function that introduces new variables
to the environment one at a time, we need some way to ``promise'' that
in the end $m$ will be equal to $n$. As can be seen in the definition
of the |Base| constructor, this is exactly what happens.

The same thing is necessary in some of the other functions, given
that they also recursively construct or look up proofs that need to
have the same size as their |BoolExpr| argument. Because they use the same
technique in a slightly less overt manner they are not separately
detailed here.

We also provide the simple lemma |zeroleast|, which shows that for any 
two $k$ and $n$, $n$ steps are needed to count from $k$ to $k+n$.


\paragraph{Soundness} Since |Diff| has been explained, and we now we finally know our real decision function |foralls|, we can set about proving its
soundness. Following the evens example, we want a function something like this.

\begin{shade}
\begin{spec}
sound : {n : ℕ} → (b : BoolExpr n) → foralls b → ...
\end{spec}
\end{shade}
What should the return type of the |sound| lemma be? We would like to
prove that the argument |b| is a tautology, and hence, the |sound|
function should return something of the form |(b1 ... bn : Bool) -> P
B|, where |B| is an expression in the image of the interpretation
|⟦_⊢_⟧|. For instance, the statement |exampletheorem| is a proposition
of this form.

The function |proofGoal|, given a |BoolExpr n|, generates the
corresponding proof obligation. That is, it gives back the type  equal to the theorem  under scrutiny. It does this by
first introducing $m$ universally quantified Boolean
variables. These variables are accumulated in an environment. Finally, when $m$
binders have been introduced, the |BoolExpr| is evaluated under this
environment.


\begin{shade}
\begin{code}
proofGoal      : (n m : ℕ) → Diff n m → BoolExpr m → Env n → Set
proofGoal   .  m    m    (Base    ) b acc = P ⟦ acc ⊢ b ⟧ 
proofGoal      n    m    (Step y  ) b acc =
               (a : Bool) →
                    proofGoal (1 + n) m y b (a ∷ acc)
\end{code}
\end{shade}


Now that we can interpret a |BoolExpr n| as a theorem using |proofGoal|, and we have a
way to decide if something is true for a given environment, we still
need to show the soundness of our decision function |foralls|. That is, we need
to be able to show that a formula is true if it holds for every
possible assignment of its variables to |true| or |false|.




\ignore{
\begin{code}
Error-elim : ∀ {Whatever : Set} {e : String} → Error e → Whatever
Error-elim ()
\end{code}
}

\begin{shade}
\begin{code}
soundnessAcc :   {m : ℕ} →          (b : BoolExpr m) →
                 {n : ℕ} →          (env : Env n) →
                 (d : Diff n m) →   forallsAcc b env d →
                 proofGoal n m d b env
soundnessAcc     bexp     env Base     H with ⟦ env ⊢ bexp ⟧
soundnessAcc     bexp     env Base     H | true  = H
soundnessAcc     bexp     env Base     H | false = Error-elim H
soundnessAcc {m} bexp {n} env (Step y) H =
  λ a → if {λ b → proofGoal (1 + n) m y bexp (b ∷ env)} a
    (soundnessAcc bexp (true  ∷ env)    y (proj₁ H))
    (soundnessAcc bexp (false ∷ env)    y (proj₂ H))
\end{code}
\end{shade}


If we look closely at the definition of |soundnessAcc|, we see that it
builds up the environment by assigning some configuration of |true| and |false| to the variables. It eventually returns the
leaf from |foralls| which is the proof that the formula is a tautology
in that specific case. 
\begin{shade}
\begin{code}
soundness       : {n : ℕ} → (b : BoolExpr n) → foralls b
                → proofGoal 0 n (zeroleast 0 n) b []
soundness {n} b i = soundnessAcc b [] (zeroleast 0 n) i
\end{code}
\end{shade}
The function |soundness| calls
|soundnessAcc| with some initial input, namely the |BoolExpr n|, an
empty environment, and the |Diff| proof that |soundnessAcc| will be called
($n-0$) times. This results in an environment of size $n$ everywhere
the expression is to be evaluated.



Now, we can prove theorems by calling |soundness b p|, where |b| is the
representation of the formula under consideration, and |p| is the evidence
that all branches of the proof tree are true. Agda is convinced
that the representation does in fact correspond to the concrete
formula, and also that |soundness| gives a valid proof. In fact, we need not
even give |p| explicitly; since the only valid values of |p| are nested pairs of |tt|,
the argument can be inferred automatically, if its type is inhabited.

If the module
passes the type checker, we know our formula is both a tautology and
that we have the corresponding proof object at our disposal
afterwards, as in the example of Fig.~\ref{fig:dup}.

\begin{shadedfigure}[h]
\begin{code}
rep          : BoolExpr 2
rep          = Imp    (And (Atomic (suc zero)) (Atomic zero)) 
                      (Atomic zero)

someTauto    : (p q : Bool)         → P( p ∧ q ⇒ q )
someTauto    = soundness rep _
\end{code}
\caption{An example Boolean formula, along with the transliteration to a proposition and the corresponding proof.}\label{fig:dup}
\end{shadedfigure}

Having said that, the trick of letting Agda infer the proof argument to pass to |soundness| is 
still a little deceptive, as explained in Sec.~\ref{sec:implicit-unit}.
The thing is, we do not want a user to get away with being able to prove that something which is not a
tautology, is a tautology. Since the proof that under all environments the theorem evaluates
to true is an inferred argument in this style, one is merely left with an unsolved meta (with an uninhabitable type, to be fair), which
might seem a triviality if you do not read the compiler's output carefully. Luckily Agda disallows
importing modules with unsolved metas, which means such a spurious proof will not be usable elsewhere
in a real-life development. 

Other than that potential pitfall, the only part we still have to do manually is to convert the concrete
Agda representation (|p ∧ q ⇒ q|, in this case) into our abstract
syntax (|rep| here). This is unfortunate, as we end up typing out the
formula twice. We also have to count the number of variables
ourselves and convert them the to De Bruijn indices. This is
error-prone given how cluttered the abstract representation can get
for formulae containing many variables. 

It would be desirable for this representation
process to be automated. Luckily we have the |Autoquote| library,
which we will apply in Sec.~\ref{sec:addrefl}.


\subsection{Why Not Enumerate Environments?}\label{sec:no-enumerate-environments}

A reasonable question to pose, after seeing the interface to the tautology prover, is why we have to separately 
introduce fresh variables. Why can we not just write something like |∀ (e : Env n) → P someprop|?

One of the reasons for not enumerating environments  is that
referring to variables inside |someprop| becomes a bit of a problem. 
Some new syntax would have to be introduced, such as a constructor
|Var : Fin n → Bool| which could be used to refer to an element of the environment by number. This is 
rather less elegant than the current implementation, which simply brings a few Boolean variables into scope in
the native Agda manner, using a telescope (i.e. |(p q r : Bool) → P(p ∧ q ⇒ r)|, as defined in Sec.~\ref{para:telescopes}). This has another advantage, namely
that when writing down a proposition, you are forced to use only valid variables, which translate to in-scope De Bruijn indices.

Another difficulty of enumerating environments is the generation of the proof goal. Currently, a telescope with Boolean variables
can be generated easily via recursion (see the function |proofGoal|), as opposed to having to generate all possible 
lists of assignments. Some investigation was done to try and show that environments (lists of Booleans) of length $n$ are enumerable,
but the results were not as elegant as those presented here. Also, generating the environments by quantifying over
fresh variables and adding them to an accumulating environment saves 
the hassle of creating a large binary tree with all the possible
environments in the leaves.



\subsection{Adding Reflection}\label{sec:addrefl}

It might come as a surprise that in a project focusing on reflection in Agda, in the programming language technology sense, has not yet
found an application for reflection in this chapter. This is about to change. 
We can get rid of the duplication seen in Fig.~\ref{fig:dup} using Agda's reflection API. 
There we see the same Boolean formula twice: once in the type signature as an Agda
proposition and once in the |BoolExpr| AST. More
specifically, we will use the |quoteGoal| keyword to inspect the
current goal. Given the |Term| representation of the goal, we can
convert it to its corresponding |BoolExpr| automatically.

\ignore{
\begin{code}
open import Proofs.TautologyProver hiding (concrete2abstract; BoolExpr; foralls; proveTautology; soundness; boolTable; term2boolexpr'; stripSo ; isSoExprQ ; proofGoal)

{-
Unfortunately, we need to duplicate this code here, because the So which is
quoted in isSoExprQ is not the same So as in the library. Oh well, this works.
-}

-- a check-function, or predicate, to determine if the thing which has
-- been quoted is a Term wrapped in a call to So(), which P()
-- normalises to.
isSoExprQ : (t : Term) → Set
isSoExprQ (var x args) = ⊥
isSoExprQ (con c args) = ⊥
isSoExprQ (def f args) with Data.Nat._≟_ (length args) 2
isSoExprQ (def f args) | yes p with tt
isSoExprQ (def f [])                   | yes () | tt
isSoExprQ (def f (x ∷ []))             | yes () | tt
isSoExprQ (def f (a ∷ arg v r x ∷ [])) | yes p  | tt with f ≟-Name quote So
isSoExprQ (def f (a ∷ arg v r x ∷ [])) | yes p₁ | tt | yes p = ⊤
isSoExprQ (def f (a ∷ arg v r x ∷ [])) | yes p  | tt | no ¬p = ⊥
isSoExprQ (def f (x ∷ x₃ ∷ x₄ ∷ args)) | yes () | tt
isSoExprQ (def f args)                 | no ¬p with tt
isSoExprQ (def f [])                   | no ¬p | tt = ⊥
isSoExprQ (def f (x ∷ xs))             | no ¬p | tt = ⊥
isSoExprQ (lam v t)                  = ⊥
isSoExprQ (pi t₁ t₂)                   = ⊥
isSoExprQ (sort x)                     = ⊥
isSoExprQ unknown                      = ⊥

-- assuming the predicate isSoExprQ above, return the
-- argument to So, which should be the boolean expression
-- we want.
stripSo : (t : Term) → isSoExprQ t → Term
stripSo (var x args)                 ()
stripSo (con c args)                 ()
stripSo (def f args)                 pf with Data.Nat._≟_ (length args) 2
stripSo (def f args) pf | yes p with tt -- doing "with tt" at the end
                                        -- is necessary in some cases,
                                        -- to force normalisation of preceding
                                        -- arguments.
stripSo (def f [])                   pf | yes () | tt
stripSo (def f (x ∷ []))             pf | yes () | tt
stripSo (def f (a ∷ arg v r x ∷ [])) pf | yes p  | tt with f ≟-Name quote So
stripSo (def f (a ∷ arg v r x ∷ [])) pf | yes p₁ | tt | yes p = x
stripSo (def f (a ∷ arg v r x ∷ [])) () | yes p  | tt | no ¬p
stripSo (def f (x ∷ x₃ ∷ x₄ ∷ args)) pf | yes () | tt
stripSo (def f args)                 pf | no ¬p with tt
stripSo (def f [])                   () | no ¬p | tt
stripSo (def f (x ∷ xs))             () | no ¬p | tt
stripSo (lam v t)                  ()
stripSo (pi t₁ t₂)                   ()
stripSo (sort x)                     ()
stripSo unknown                      ()

\end{code}
}

The conversion between a |Term| and |BoolExpr| is achieved using the function \mbox{|concrete2abstract|}.
\begin{shade}
\begin{code}
concrete2abstract    :     (t     : Term)        → (n : ℕ)
                     →     {pf    : isSoExprQ (stripPi t)}
                     →     {pf2   : isBoolExprQ n (stripPi t) pf}
                     →     BoolExpr n
\end{code}
\end{shade}
\ignore{
\begin{shade}
\begin{code}
concrete2abstract t n {pf} {pf2} = doConvert --  term2boolexpr n (stripSo (stripPi t) pf) pf2
\end{code}
\end{shade}}\!\!
Note that not every |Term| can be converted to a |BoolExpr|. Looking at the type signature of the 
|concrete2abstract| function, we see that it requires additional assumptions about the
|Term|: it may only contain functions such as |_∧_| or |_∨_|, and
bound variables. This is ensured by the predicates
|isBoolExprQ| and friends.

The |concrete2abstract| function is rather verbose, and is mostly omitted.
A representative snippet is given in Fig.~\ref{fig:concrete2abstract}. The attentive reader will notice that
the function in the referenced figure is called |term2boolexpr|; this is because we also unwrap the outermost call to |P| 
and the telescope quantifying over  the variables before doing the conversion, since these elements are unnecessary in the |BoolExpr| representation. 
The function |term2boolexpr| can be seen as a helper function to |concrete2abstract| where the ``interesting''  work happens.
The functions in the type signature, |isBoolExprQ|
and |isSoExprQ|, simply traverse the |Term| to see if it fulfils the requirements of
being a Boolean expression enclosed in a call to |P|, preceded by a series of universally quantified Boolean variables.



All these pieces are assembled in the |proveTautology| function.

\begin{shade}
\begin{code}
proveTautology :    (t     : Term) →
                    {pf    : isSoExprQ (stripPi t)} →
                    let n = freeVars t in
                        {pf2   : isBoolExprQ n (stripPi t) pf} →
                        let b = concrete2abstract t n {pf} {pf2} in
                            {i : foralls b} →
                            proofGoal 0 n (zeroleast 0 n) b []
proveTautology t {_}{_}{i} = 
  soundness (concrete2abstract t (freeVars t)) i
\end{code}
\end{shade}
%TODO this is irrelevant!
The |proveTautology| function converts a raw |Term| to a |BoolExpr n|
format and calls the |soundness| lemma. It uses a few auxiliary
functions such as |freeVars|, which counts the number of variables
(needed to be able to instantiate the $n$ in |BoolExpr n|), and
|stripSo| \& |stripPi|, which peel off the universal quantifiers and the
function |So| with which we wrap our tautologies. These helper
functions have been omitted for brevity, since they are rather
cumbersome and add little to the understanding of the subject at
hand.


These are all the ingredients required to automatically prove that
formulae are tautologies.  The following code illustrates the use of
the |proveTautology| functions; we can omit the implicit arguments for
the reasons outlined in Sec.~\ref{sec:implicit-unit}.

\begin{shade}
\begin{code}
exclMid    : (b : Bool) → P(b ∨ ¬ b)
exclMid    = quoteGoal e in proveTautology e

peirce     : (p q : Bool) → P(((p ⇒ q) ⇒ p) ⇒ p)
peirce     = quoteGoal e in proveTautology e

fave       : exampletheorem -- defined in Fig.~\ref{fig:exampletheorem}
fave       = quoteGoal e in proveTautology e
\end{code}
\end{shade}


This shows that the reflection capabilities recently added to Agda are quite useful for
automating certain tedious tasks, since we now need not encode the Boolean expression
twice, in  slightly different formats. The conversion now happens automatically, without loss
of expressive power or general applicability of the proofs resulting from |soundness|.
Furthermore, by using the proof by reflection technique, the proof is generated automatically.

It seems conceivable to imagine that in the future, using techniques such as those presented
here, a framework for tactics might be within reach. Eventually we might be able to define an
embedded language in Agda to inspect the shape of the proof that is needed, and look at a database
of predefined proof recipes to see if one of them might discharge the obligation. An advantage of 
this approach versus the tactic language in Coq, would be that the language of the propositions and
tactics is the same.

The attentive reader will remember that we previously studied a system capable of automatically
quoting concrete Agda to a simple user-defined AST. Would that not be perfectly suited to quoting to 
the |BoolExpr| type used here? This turns out to be the case: we exploit this possibility in the rest of this chapter.

\subsection{An Aside: Real-world Example of Automatic Quoting}\label{sec:autoquote-example}

The process of quoting to a |BoolExpr n| outlined in Sec.~\ref{sec:addrefl}
quickly becomes an ugly mess, with functions checking properties of an expression (such
as only certain functions like |_∧_| or |¬_| occurring in the |Term|) being repetitive and verbose. The code summarised 
in Fig.~\ref{fig:concrete2abstract} is an example of such a mess. If one 
then wanted to quote to some other AST, the whole process would have to be modified, which, I can guarantee,
is a painful process.

The actual conversion function also ends up having many branches, checking if all the
constructors and definitions are recognised, etc. This process can be made a lot less ugly and a lot more reusable.
Recall the |Autoquote| module developed in
Sec.~\ref{sec:autoquote}; the same can be used here, both as an
illustration of its use, and to avoid code duplication,
thus making the code for |term2boolexpr| more concise.

|Autoquote| only supports simple inductive data types, so the first problem we encounter is that
|BoolExpr n| has an argument of type |Fin n| to its constructor |Atomic| (see Fig.~\ref{fig:boolexprn}).
To work around this, we introduce a simpler, intermediary data structure, to which we will convert
from |Term|. This type, called |BoolInter|, is presented in Fig. \ref{fig:boolinter}. It has no such constraints.

\begin{shadedfigure}[h]
\begin{code}
data BoolInter : Set where
  Truth        :                                  BoolInter
  Falsehood    :                                  BoolInter
  And          : BoolInter     → BoolInter    →   BoolInter
  Or           : BoolInter     → BoolInter    →   BoolInter
  Not          : BoolInter                    →   BoolInter
  Imp          : BoolInter     → BoolInter    →   BoolInter
  Atomic       : ℕ                            →   BoolInter
\end{code}
\caption{An intermediary data type, which is a simplified (constraint-free) version of |BoolExpr n|.}\label{fig:boolinter}
\end{shadedfigure}

The mapping needed for |Autoquote| is as follows: we mention which constructor represents
De Bruijn-indexed variables and what the arity is of the different constructors. This way
only |Term|s containing variables or the operators and, or, not,
implication, true or false are accepted. Using this mapping, we can
construct the function |term2boolexpr'| that, for suitable |Term|s,
gives us an expression in |BoolInter|. See Fig.~\ref{fig:booltable}.

\begin{shadedfigure}[h]
\begin{code}
boolTable : Table BoolInter
boolTable = (Atomic ,
                  2 \# (quote _∧_      ) ↦ And
            ∷     2 \# (quote _∨_      ) ↦ Or
            ∷     1 \# (quote  ¬_      ) ↦ Not
            ∷     0 \# (quote true     ) ↦ Truth
            ∷     0 \# (quote false    ) ↦ Falsehood
            ∷     2 \# (quote _⇒_      ) ↦ Imp ∷ [])

term2boolexpr'     : (t : Term)
                   → {pf : convertManages boolTable t}
                   → BoolInter
term2boolexpr' t {pf} = doConvert boolTable t {pf}
\end{code}
\caption{The mapping table for quoting |BoolInter|.}\label{fig:booltable}
\end{shadedfigure}

Once we have a |BoolInter| expression, we just need to check that its
variables are all in scope (this means that $\forall$ |Atomic| $x  :     x < n$, if we
want to convert to a |BoolExpr n|). This is done in |bool2fin|, assuming that |bool2finCheck|
holds (the latter simply expresses the in-scope property).

\begin{shade}
\begin{spec}
bool2finCheck : (n : ℕ) → (t : BoolInter) → Set
bool2finCheck n Truth        = ⊤
bool2finCheck n (And t t₁)   = bool2finCheck n t × bool2finCheck n t₁
...
bool2finCheck n (Atomic x)   with suc x ≤? n
bool2finCheck n (Atomic x)   | yes p    = ⊤
bool2finCheck n (Atomic x)   | no ¬p    = ⊥

bool2fin : (n : ℕ) (t : BoolInter) (bool2finCheck n t) → BoolExpr n
bool2fin n Truth        pf            = Truth
bool2fin n (And t t₁)   (p₁ , p₂)     = And (bool2fin n t p₁) (bool2fin n t₁ p₂)
...
bool2fin n (Atomic x)  p₁       with suc x ≤? n
bool2fin n (Atomic x)  p₁       | yes p    = Atomic (fromℕ≤ {x} p)
bool2fin n (Atomic x)  ()       | no ¬p
\end{spec}
\end{shade}

With these ingredients, our |concrete2abstract| function presented in Sec.~\ref{sec:addrefl}
can be rewritten to the following  drop-in replacement, illustrating how useful such an
abstraction can be.  It uses the function |term2boolexpr'| defined in Fig.~\ref{fig:booltable}.

\begin{shade}
\begin{spec}
concrete2abstract' :
         (t : Term)
       → {pf : isSoExprQ (stripPi t)}
       → let t' = stripSo (stripPi t) pf in
            {pf2 : convertManages boolTable t'}
          → (bool2finCheck (freeVars t) (term2boolexpr' t' {pf2}))
          → BoolExpr (freeVars t)
concrete2abstract' t {pf} {pf2} fin = bool2fin     (freeVars t)
                                                   (term2boolexpr'
                                                     (stripSo (stripPi t) pf)
                                                     {pf2})
                                                   fin
\end{spec}
\end{shade}

Clearly, the |Autoquote| module can save a lot
of repetitive coding for converting |Term|s into some  more structured
AST, such as |BoolExpr n|. 

Finally, all developments regarding the proof by reflection technique, including
the quoting code can be found in the modules |Proofs.TautologyProver| and |Metaprogramming.Autoquote|, respectively.
There are also examples of using the tautology prover as a library in |Proofs.ExampleTautologies|, as well as two examples
of using |Autoquote| in |Metaprogramming.ExampleAutoquote|. 
The more extensive illustration of what is possible using |Autoquote| can be
found in |Proofs.TautologyProver|.




\section{Discussion}\label{sec:discussion}
% ... and Conclusion and Related Work and Reflection API Limitations

 
 
 
 
This project's main innovations are novel combinations of existing
techniques; as a result, quite a number of subjects are relevant to mention
here.
 
As far as reflection in general goes, Demers and Malenfant \cite{demers1995reflection} wrote an informative historical overview on the topic.
What we are referring to as reflection dates back to work by Brian Smith \cite{Smith:1984:RSL:800017.800513}
and was initially presented in the Lisp family of languages in the 80s. Since then,
many developments in the functional, logic as well as object-oriented programming worlds have 
been inspired~-- systems with varying power and scope.
 
 
People sometimes jokingly say that the more advanced
a given programming language becomes, the more it converges towards Lisp \cite{graham04}, and that
the more complex some piece of software becomes, the higher the likelihood of discovering somewhere in
the source a badly defined, ad hoc implementation of a Lisp interpreter.
The fact is, though, that it is becoming increasingly common to generate pieces of code 
from a general recipe, possibly giving rise to a more efficient specific implementation, 
or at the very least not having to reinvent the wheel. Reflection is becoming more common, to
various extents, in industry-standard languages such as Java, Objective-C, as well as theoretically more interesting
languages, such as Haskell \cite{DBLP:journals/lisp/Stump09}. Smalltalk, an early
object-oriented programming language with advanced reflective features \cite{Goldberg:1983:SLI:273}, is the predecessor of Objective-C. As such, it
is surprising that industry programming does not use more of these advanced reflective features which have already  been around for a 
long time.
 
This would seem to be the inspiration for the current reflection system recently introduced
in Agda, although we shall see that it is lacking in a number of fundamental capabilities.
If we look at the taxonomy of reflective systems in programming language technology written up 
by Sheard \cite{sheard-staged-programming}
we see that we can make a few rough judgements about the metaprogramming facilities Agda currently 
supports\footnote{Of course, having been implemented during a single  Agda Implementors' Meeting \cite{thorsten-communication}, the current implementation is more a proof-of-concept, and is still far from
being considered finished, so it would be unfair to judge the current implementation all too harshly. In
fact, I hope that this work might motivate the Agda developers to include some more features, to
make the system truly useful. }.
 
\begin{itemize}
\item Agda's current reflection API leans more towards analysis than generation,
\item it supports encoding of terms in an algebraic data type (as opposed to a string, for example),
\item it involves manual staging annotations (by using keywords such as |quote| and |unquote|),
\item it is neither strictly static nor run time, but compile time. It behaves much like a 
  static system (one which produces an object program, as does for example YAcc \cite{johnson1975yacc})
  would, but does not produce intermediate code which might be modified later by the user.
  Note that this fact is essential for Agda to remain sound.
\item It is homogeneous, because a representation of the object language lives inside the metalanguage (as a native
  data type), 
\item it is only two-stage: we cannot as yet produce an object program which is itself a metaprogram. This is
  because we rely on built in keywords such as |quote|, which cannot themselves be represented.
\end{itemize}
 
 
 
 
 
As far as the proof techniques used in the section on proof by reflection (Sec.~\ref{sec:proof-by-reflection}) are concerned,  
Chlipala's work \cite{chlipala2011certified} proved an invaluable resource, both for inspiration and guidance. One motivating example
for doing this in Agda was Wojciech Jedynak's ring solver \cite{ringsolver}, which is the first example of Agda's reflection
API in use that came to our attention. Compared to Jedynak's work, the proof generator presented here is more refined in terms of the interface
presented to the user. The expectation is that approaches like these will become more commonplace for proving mundane lemmas in 
large proofs. The comparison to tactics in a language like Coq is a natural one, and we see both advantages and disadvantages of each style. Of course, 
the tactic language in Coq is much more specialised and sophisticated when it comes to generating proofs, but it is a pity that there are
two separate languages in one, instead of the Agda way, where metaprograms are written directly in the object language. Also, the 
fact that proof generation in Agda is explicit may be something some people appreciate. (Far) future work might be to 
implement some sort of tactic framework for Agda, possibly with a DSL in the style of Coq's tactic language, around the reflection API.
% Uh the following sentence sucks.
The Ssreflect extension for Coq \cite{gonthier:inria-00515548}  should also be mentioned here; because of a lack of experience with Ssreflect, I 
refrain from making concrete statements, but the expectation is that
the developments presented here should also be possible using
Ssreflect.\todo{get familiar with ssreflect or fix the statement}
 
Returning to our research question,  repeated here to jog the memory,  a summary of findings is made.

\researchquestion

This paper has presented two simple applications of proof by
reflection, the latter using Agda's reflection API. 

We 
have managed to automate generation of a certain class of proofs, which certainly 
would count as mundane. The clear advantage of Agda's reflection system is that it
leverages the power of Agda's dependent types. Unfortunately, though,
the reflection API itself is still rather primitive, so we find ourselves unable to define 
things such as an automatic Bove-Capretta transformation of a given function, or the generation
of generic programming embedding and projection functions. The reasons for not being able to 
do all that we would like with the API as it stands are best summarised as follows. 
 
%Reflection API limitations:
\begin{itemize}
\item One cannot call |unquote| on nonconstructor terms,
i.e. |unquote (lam2term t)| where $t$ is some parameter or variable.
\item It is impossible to introduce definitions, and therefore also
impossible to define pattern matching, since pattern matching is only
allowed in definitions. Pattern matching lambda expressions in Agda
are simply syntactic sugar for local definitions. This precludes
automating the Bove-Capretta method, and makes generic programming
techniques all the more painful.
\item Inspection of functions (e.g. clauses) is not implemented, although
inspection of data type definitions is quite comprehensive.
\item By default, untyped terms are returned from the |quoteTerm|
keyword. This has been solved in the patches presented in
the mentioned thesis \cite{vdWalt:Thesis:2012}, but these are yet to be
included in the main development version of Agda.
\item The |unquote| keyword is unaware of types, so even if a program transformation is
  type-safe, in the end unquoting is still hit-and-miss.
\end{itemize}
 

Having said all of that, though, a number of things are possible with the reflection mechanism 
as it stands, and the expectation is that it should be possible to define quite a few more examples
of program transformations and proof generators which will likely turn out to be useful for various
niche applications.
 
 
\newpage
% \phantomsection \label{listoffig}
% \addcontentsline{toc}{chapter}{List of Figures}
% \listoffigures

\bibliography{refs}{}
%\bibliographystyle{plain}
% for LNCS bibliography:
\bibliographystyle{splncs}%this one doesn't sort automatically. :(



% Voor IFL paper:
% Beperk je tot de essentie
% Geef voorbeelden



\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-parse-self: t
%%% TeX-master: t
%%% TeX-command-default: "lagda2pdf"
%%% End: 
