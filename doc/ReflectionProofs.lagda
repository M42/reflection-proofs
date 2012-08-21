\documentclass[a4paper]{report}
%\documentclass[a4paper]{llncs}


%include polycode.fmt
%if style == newcode
%else
%include agda.fmt
%include generated-colour.fmt
%include codecolour.fmt
%endif

\usepackage{todonotes}
\newcommand{\ignore}[1]{}

\newcommand{\pref}[1]{~\ref{#1} on page~\pageref{#1}}

\def\CC{{C\nolinebreak[4]\hspace{ -.05em}\raisebox{.4ex}{\tiny\bf ++}}}

\ignore{
\begin{code}
module ReflectionProofs where
\end{code}


\begin{code}
-- imports for Evenness
open import Relation.Binary.PropositionalEquality
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Bool hiding (T) renaming (not to ¬_) 
open import Data.Nat renaming (_≟_ to _≟-Nat_)
\end{code}
}

\ignore{
\begin{code}
-- imports for Boolean tauto solver
open import Data.String using (String)
open import Relation.Nullary hiding (¬_)
open import Data.Product hiding (map)
open import Relation.Binary hiding (_⇒_)
open import Reflection

open import Data.Fin hiding (_+_; pred )
open import Data.Vec renaming (reverse to vreverse ; map to vmap; foldr to vfoldr; _++_ to _v++_ ; _∈_ to _vecin_)
open import Data.Unit hiding (_≤?_)
open import Data.Empty
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.List hiding (_∷ʳ_)
\end{code}
}

\usepackage{amsmath}


\usepackage{hyperref}
\usepackage{url}

\author{Paul van der Walt \and Wouter Swierstra}
\date{\today}
\title{Applications of Reflection in Agda}
%%\institute{
%%\href{mailto:paul@@denknerd.org}{\nolinkurl{paul@@denknerd.org}}, \href{mailto:W.S.Swierstra@@uu.nl}{\nolinkurl{W.S.Swierstra@@uu.nl}}\\
%%Department of Computer Science, Utrecht University
%%}


%TODO add citations to everything which seems like an unfounded statement.

\begin{document}

\maketitle
%TODO make a fancy title page

\clearpage
\thispagestyle{empty}
\vspace*{\fill} 
\begin{quote} 
\centering 
\emph{``Using Coq is like doing brain surgery over the telephone.''}
\end{quote}
\vspace*{\fill}
\clearpage

\tableofcontents
\clearpage

%\begin{abstract}
%  This paper explores the recent addition to Agda enabling
%  \emph{reflection}, in the style of Lisp, MetaML, and Template
%  Haskell. It illustrates several applications of reflection that
%  arise in dependently typed programming.
%\end{abstract}

\chapter{Introduction}

Since the inception of computer programming, the aim has often been to
write as concise code as possible, while achieving the most powerful effect.
One of the holy grails of writing programs is also being able to reuse pieces of
code, after having written them once, as opposed to continually writing small
variations on existing code. Reinventing the wheel is something a programmer
should not enjoy doing.

One of the many techniques invented to allow writing more effective
code is that of \emph{metaprogramming}, which, in vague terms, refers
to the ability of a program to inspect (or \emph{reflect}) its own code
and modify it. To the uninitiated, this sounds rather magical \cite{reflection-stackoverflow},
but has long been a favourite
feature of users of such languages as LISP~\cite{lisp-macros}, in many cases allowing
code to be a lot more concise and general, and thus reusable, than 
usually is possible in simple imperative languages.





The dependently typed programming language
Agda~\cite{norell:thesis,Norell:2009:DTP:1481861.1481862} has recently been
extended with a \emph{reflection mechanism} for compile time meta
programming in the style of Lisp~\cite{lisp-macros},
MetaML~\cite{metaml}, Template Haskell~\cite{template-haskell}, and
\CC\ templates~\cite{cplusplus}. Agda's reflection mechanisms makes it
possible to convert a program fragment into its corresponding abstract
syntax tree and vice versa. In tandem with Agda's dependent types,
this provides promising new programming potential. 


The main question which we aim to answer during this project is:


\begin{quote}
``Given the new reflection API in Agda, what interesting applications can we give
examples of? Which tedious and mundane tasks can we automate? What advantages
does Agda's implementation of reflection have over other languages
 which already have reflection, and, finally, is
it adequate as it stands to facilitate our needs or does it need extension? If
extension is necessary, how much?''
\end{quote}



This paper starts exploring the possibilities and limitations of this
new reflection mechanism. It describes several case studies,
exemplative of the kind of problems that can be solved using
reflection. More specifically it makes the following contributions:

%TODO: do I want to use the more extensive itemize points from
%introduction.tex? These here are the condensed version for the IFL paper
\begin{itemize}
\item This paper documents the current status of the reflection
  mechanism. The existing documentation is limited to a paragraph in
  the release notes~\cite{agda-relnotes-228} and comments in the
  compiler's source code. In Chapter~\ref{sec:reflection} we give
  several short examples the reflection API in action.
\item This paper illustrates how to use Agda's reflection mechanism to
  automate certain categories of proofs
  (Chapter~\ref{sec:proof-by-reflection}). The idea of \emph{proof by
    reflection} is certainly not new, but still worth examining in the
  context of this new technology.
  
\item We show how to
  guarantee \emph{type safety of meta-programs}. To illustrate this
  point, we will develop a type safe translation from the simply typed
  lambda calculus to combinatory logic, followed
by a type-safe translation of closed lambda terms into SKI combinator calculus (Chapter~\ref{sec:type-safe-metaprogramming}).
 
\item A number of neat examples are given on how to automate certain
  aspects of modifying a program to use generic programming techniques in Chapter~\ref{sec:generic-programming}. 

\item Finally, we also discuss some of the
  limitations of the current implementation of reflection (Sec.~\ref{sec:reflection-api-limitations}).
\end{itemize}

The code and examples presented in this paper all compile using the
latest version of Agda 2.3.0.1 and are available on
github.\footnote{\url{http://www.github.com/toothbrush/reflection-proofs}} %TODO this isn't true.

\chapter{Related Work}

% TODO : Mention mcbride with ornaments; 


% TODO : I would like to do something like this:
% 
% cs : (A : Set) → List Name -- give a list of constructors
% cs type = ... quote type ...
% 
% but I can't, because type isn't a defined thing. if I try to use quoteTerm here, I just get
% something like var 0 [], which of course also isn't useful. I would actually like the same as
% `quote Col`, for example. i.e. a QName I can actually use.
% 
% The same sort of problem holds for unquote: I can't do `unquote (somethingreturningaTerm ...)`
% because at compile-time it's not always clear that the function `somethingreturningaTerm`
% will return a bunch of constructors of Term. What we need is delayed or lazy quoting, maybe.


This project's main innovations are the novel combinations of existing
techniques; therefore quite a number of subjects are relevant to mention
here.

As far as reflection in general goes, Demers and Malenfant \cite{demers1995reflection} wrote a nice historical overview on the topic.
What we are referring to as reflection dates back to work by Brian Smith \cite{Smith:1984:RSL:800017.800513}
and was initially presented in the Lisp family of languages in the 80's. Since then,
many developments in the functional, logic as well as object-oriented programming worlds have 
been inspired -- systems with varying power and scope.


People sometimes jokingly say that the more advanced
a given programming language becomes, the more it converges towards Lisp \cite{graham04}.
The fact is, though, that it is becoming increasingly common to generate pieces of code 
from a general recipe, giving rise to possibly a more efficient specific implementation, 
or at the very least not having to reinvent the wheel. Reflection is becoming more common, to
various extents, in industry-standard languages such as Java, Objective-C, as well as theoretically more interesting
languages, such as Haskell \cite{DBLP:journals/lisp/Stump09}.

This would seem to be the inspiration for the current reflection system recently introduced
in Agda, although we shall see that it is lacking in a number of fundamental capabilities.
If we look at the taxonomy of reflective systems in programming language technology written up 
by Sheard \cite{sheard-staged-programming}
we see that we can make a few rough judgments about the metaprogramming facilities Agda currently 
supports\footnote{Of course the current implementation is more a proof-of-concept, and is still far from
being considered finished, so it would be unfair to judge the current implementation all too harshly. In
fact, the author hopes that this work might motivate the Agda developers to include some more features, to
make the system truly useful. 
}. \todo{ is this not becoming more of a discussion / conclusion?}

Agda's reflection API\ldots
\begin{itemize}
\item leans more towards analysis than generation
\item supports encoding as an algebraic data type (as opposed to a string, for example)
\item involves manual staging annotations (with keywords such as |quote| and |unquote|)
\item is neither strictly static nor runtime, but compile-time. This behaves much like a 
  static system (one which compiles an object program, as does for example YAcc%todo cite
) would, but doesn't produce intermediate code which might be modified.
  Note that this fact is essential for Agda to remain sound as a logical framework.
\item is homogeneous, in that the object language lives inside the metalanguage (as a native
  data type), but
\item is only two-stage: we cannot as yet produce an object program which is itself a metaprogram. This is
  because we rely on built-in keywords such as |quote|, which cannot themselves be quoted.
\end{itemize}


\todo{idea: put the above in discussion, and just mention Sheard's taxonomy here.}


Other related work includes the large body of publications in the
domain of generic programming
\cite{Rodriguez:2008:CLG:1543134.1411301,mcbride2010ornamental}, where we found the
inspiration to try and implement some of the techniques in a
dependently-typed setting.

Program transformations and their correctness (by various definitions) have long been a subject of research \cite{Partsch:1983:PTS:356914.356917},
and given more advanced languages with more powerful generative programming techniques, this will likely prove a continuing trend.

As far as the proof techniques used in the section on proof by reflection (Chapter~\ref{sec:proof-by-reflection}) is concerned,  
Chlipala's work \cite{chlipala2011certified} proved an invaluable resource, both for inspiration and guidance. One motivating example
for doing this in Agda was Wojciech Jedynak's ring solver \cite{ringsolver}, which was the first example of Agda's reflection
API in use that came to our attention.




\chapter{Reflection in Agda}
\label{sec:reflection}

Since version 2.2.8, Agda includes a reflection API, which allows converting
parts of a program's code into abstact syntax, in other words a data structure
in Agda itself, which can be inspected or modified like any other data structure.
The idea of reflection is nothing new: already in the 1980's LISP included a similar
feature, called quoting, which allowed run-time modification of a program's code, by
the program itself. This gives rise to powerful techniques for reusing code and
generating frequently needed but slightly different expressions automatically.

%TODO give more of an intro to the idea of reflection here. idea: wikipedia has short article on reflection.

\section{The Basics}

Agda's reflection API defines several data types which represent terms,
types, and sorts. These definitions take into account various
features, including hidden arguments and computationally irrelevant
terms. An overview of the core data types involved has been
included in Figure~\ref{fig:reflection}. In addition to these data
types that represent \emph{terms}, there is limited support for
reflecting \emph{definitions} as opposed to terms. Inspection of definitions
is detailed in Sec.~\ref{sec:inspecting-definitions}.

There are several new keywords that can be used to quote and unquote
|Term| values: |quote|, |quoteTerm|, |quoteGoal|, and |unquote|. The
|quote| keyword allows the user to access the internal representation of
any identifier. This internal representation can be used to query the
type or definition of the identifier.
The
examples discussed in this paper will not illustrate |quote|. The other quotation forms,
|quoteTerm| and |quoteGoal|, will be used.

The easiest example of quotation uses the |quoteTerm| keyword to turn
a fragment of concrete syntax into a |Term| data type. Note that the
|quoteTerm| keyword reduces like any other function in Agda. As an
example, the following unit test type checks:
\begin{code}
example₀   : quoteTerm (\ (x : Bool) -> x)
           ≡ lam visible (el _ (def (quote Bool) [])) (var 0 [])
example₀ = refl
\end{code}

Dissecting
this, we introduced a lambda abstraction, so we expect the |lam|
constructor. It's one argument is visible, and
the body of the lambda abstraction is just a reference to the
nearest-bound variable, thus |var 0|, applied to no arguments, hence
the empty list.

Furthermore, |quoteTerm| type checks and normalizes its term before
returning the required |Term|, as the following example demonstrates:
\begin{code}
example₁ : quoteTerm ((\ x → x) 0) ≡ con (quote ℕ.zero) []
example₁ = refl
\end{code}

The |quoteGoal| keyword is slightly different. It is best explained using an
example:

\begin{spec}
exampleQuoteGoal : ℕ
exampleQuoteGoal = quoteGoal e in {!!}
\end{spec}
The |quoteGoal| keyword binds the variable |e| to the |Term|
representing the type of the current goal. In this example, the value
of $e$ in the hole will be |def ℕ []|, i.e., the |Term| representing
the type |ℕ|.

Another keyword which deals with types is the aptly-named |type| function. Given
a |Name|, such as the result of |quote identifier|, |type| returns the |Type| representing the
type of that identifier. This indeed implies one cannot ask the type of an arbitrary
|Term|, since one would need to introduce it as a defition first, to be able to get its |Name|.
In |example₂| we see what |type| returns when asked about the successor function (a function with
type |ℕ → ℕ|, and in |example₃| we illustrate that the term shown is in fact the same as a
function type from naturals to naturals.

\begin{code}
example₂   : type (quote ℕ.suc)
           ≡ el (lit 0)     (pi (arg visible relevant
                                      (el (lit 0) (def (quote ℕ) [])))
                                      (el (lit 0) (def (quote ℕ) [])))
example₂ = refl

example₃   : type          (quote ℕ.suc)
           ≡ el (lit 0)    (quoteTerm (∀ (n : ℕ) → ℕ))
example₃ = refl

\end{code}


The |unquote| keyword converts a |Term| data type back to concrete
syntax. Just as |quoteTerm| and |quoteGoal|, it type checks and
normalizes the |Term| before it is spliced into the program text.






\begin{figure}[p]
%if style == poly
  \begin{spec}
      postulate Name : Set

    -- Arguments may be implicit, explicit, or inferred
      data Visibility : Set where
        visible hidden instance : Visibility


    -- Arguments can be relevant or irrelevant.
      data Relevance : Set where
        relevant irrelevant : Relevance

    -- Arguments.
      data Arg A : Set where
        arg : (v : Visibility) (r : Relevance) (x : A) → Arg A
    -- Terms.
      mutual
        data Term : Set where
        -- A bound variable applied to a list of arguments
          var     : (x : ℕ) (args : List (Arg Term)) → Term
        -- Constructor applied to a list of arguments
          con     : (c : Name) (args : List (Arg Term)) → Term
        -- Identifier applied to a list of arguments
          def     : (f : Name) (args : List (Arg Term)) → Term
        -- Lambda abstraction (including type annotation)
          lam     : (v : Visibility) (σ : Type) (t : Term) → Term
        -- Dependent function types
          pi      : (t₁ : Arg Type) (t₂ : Type) → Term
        -- Sorts
          sort    : Sort → Term
        -- Anything else
          unknown : Term

        data Type : Set where
          el : (s : Sort) (t : Term) → Type

        data Sort : Set where
        -- A Set of a given (possibly neutral) level.
          set     : (t : Term) → Sort
        -- A Set of a given concrete level.
          lit     : (n : ℕ) → Sort
        -- Anything else.
          unknown : Sort
  \end{spec}
%endif
  \caption{The data types for reflecting terms}
  \label{fig:reflection}
\end{figure}



The representation of |Term|s is de Bruijn-style,
and lambda abstractions are modeled as binding one variable. A variable has a de Bruijn index,
and may be applied to arguments.
%Note the |Type| argument in the |lam| constructor:
%this holds the type of the argument expected.

|con| and |def| are introduced when constructors and definitions, respectively,
are applied to a (possibly empty) list of arguments. Finally the constructor |unknown| is
used for things which are not or cannot be represented in this AST (such as function definitions).



A common task will be casting the raw |Term| we get into some AST of
our own.
A library has been developed which might serve as both an instructive
example in how to pull apart |Term|s, as well as a useful function,
since it provides the feature of automatically converting a |Term|
into some AST type, if a mapping is provided from concrete Agda
|Name|s to constructors of this AST. An explanation of its implementation is given
in Sec.~\ref{sec:autoquote}, and an example use-case is given in \ref{sec:autoquote-example}.


\section{List of Functions Exported by |Reflection|}

The |Reflection| module of the Agda standard library (version 0.6 was used here) exports a number of
functions. Here we will provide a list of them (see Fig. \ref{fig:reflection-functions}) along with
a description of their use.

\begin{figure}[h]
\begin{spec}
_≟-Name_ : Decidable {A = Name} _≡_
-- also list the rest of the decidable things?
-- or just leave it to peoples' imagination?

type : Name → Type
definition : Name → Definition
constructors : Data-type → List Name
\end{spec}
\caption{The functions exported by the |Reflection| module of the Agda standard library, as of version 0.6.}\label{fig:reflection-functions}
\end{figure}

As mentioned before, the way to get an object of type |Name| is by using the |quote| keyword, for
example as in |quote zero|. Once we have a |Name|, we can get more information about it.
The |type| function, unsurprisingly, tells us the type of whatever we give it, or |unknown|. For example:

\begin{code}
typeExample : type (quote ℕ.suc) ≡
            el (lit 0) (pi
              (arg visible relevant (el (lit 0) (def (quote ℕ) []))
              )
                                    (el (lit 0) (def (quote ℕ) []))
                       )
typeExample = refl
\end{code}

The right-hand side of the type of |typeExample| boils down to a function of type |ℕ → ℕ|, where the |el (lit 0) x| annotations
mean that the sort of $x$ is |Set₀| (which is the same as |Set|). 

The |definition| function returns the definition of a given identifier. The type is defined as follows.

\begin{spec}
data Definition : Set where
  function     : Function  → Definition
  data-type    : Data-type → Definition
  record′      : Record    → Definition
  constructor′ : Definition
  axiom        : Definition
  primitive′   : Definition
\end{spec}

At the time of writing the only constructor we can do anything with is |data-type|: using
it we can get a list of constructors, by calling the suitably-named |constructors| function. See the
illustration in Sec.~\ref{sec:inspecting-definitions}.

Finally, we have decidable equality on the following types: |Visibility|, |Relevance|, |List Arg|s, |Arg Type|s, |Arg Term|s,  |Name|s,  |Term|s, |Sort|s  and |Type|s. 

Typically, this is useful for deciding which constructor is present in some expression, such as:

\begin{spec}
convert : Term → Something
convert (def c args) with c ≟-Name quote foo
...                   | yes p = do_something -- foo applied to arguments
...                   | no ¬p = do_other_thing -- another function than foo
\end{spec}


\subsection{Inspecting Definitions}\label{sec:inspecting-definitions}

Using the functions exported by the module |Reflection|, we are able
to get a list of constructors for some data type. The following code snippet
illustrates how this is done, and what the format of the answer is.

\ignore{
\begin{code}
isDatatype : Definition → Set
isDatatype (data-type x) = ⊤
isDatatype _ = ⊥
\end{code}
}
\begin{code}
giveDatatype : (d : Definition) → {pf : isDatatype d} → Data-type
giveDatatype (data-type d) = d
giveDatatype (function x)   {()}
\end{code}
\vskip -7mm
\begin{spec}
...
\end{spec}
\vskip -4mm
\ignore{
\begin{code}
giveDatatype (record′ x)    {()}
giveDatatype constructor′   {()}
giveDatatype axiom          {()}
giveDatatype primitive′     {()}
\end{code}}
\begin{code}

ℕcons : List Name
ℕcons = constructors (giveDatatype (definition (quote ℕ)))

consExample : ℕcons ≡       quote ℕ.zero   ∷
                            quote ℕ.suc    ∷ []
consExample = refl
\end{code}

So now we have in |ℕcons| a list of the names of the constructors of the data type |ℕ|, which we
could use to do more interesting things which depend on the structure of a data type, such as
giving isomorphisms to generic representations of data types, such as is often done using
Template Haskell, for example in the Regular library for generic programming \cite{van2010lightweight}.
This capability is exploited in Sec.~\ref{sec:generic-programming}.





\section{Introducing |Autoquote|}\label{sec:autoquote} \todo{move this to after boolexpr? or?}

Imagine we have some AST, for example |Expr|, which is presented below.
This is a rather simple data structure representing terms which can contain Peano style natural
numbers, variables (indexed by an Agda natural) and additions.

\begin{code}
data Expr : Set where
  Variable      : ℕ               → Expr
  Plus          : Expr → Expr     → Expr
  Succ          : Expr            → Expr
  Zero          :                   Expr
\end{code}

We might concievably want to convert a piece of concrete syntax, such as $5 + x$, to this
AST, using Agda's reflection system. This typically involves ugly and verbose functions such
as the one from Sec.~\ref{sec:boolean-tautologies} with many with-clauses and frankly, too
much tedium to be anything to be proud of. What we would actually like to be able to do,
is provide a mapping from concrete constructs such as the |_+_| function to elements of our
AST, and get a conversion function for free.



During the course of this project, a module named |Autoquote| was developed. The
motivating idea behind |Autoquote| is that one often ends up writing similar-looking
functions for checking if a |Term| is of a specific shape, then if so,
translating |Term|s into some AST. What |Autoquote| does is abstract
over this process, and provide an interface which, when provided with
a mapping from concrete names to constructors in this AST,
automatically quotes expressions that fit (i.e. which only have
variables, and names which are listed in this mapping).

This is the type we use for specifying what the AST we are expecting should look like. |N-ary| provides
a way of storing a function with a variable number of arguments in our map, and |_dollarn_| is how we
apply the ``stored'' function to a |Vec n| of arguments, where $n$ is the arity of the function. Note that
this is a copy of the standard library |Data.Vec.N-ary|, but has been instantiated here specifically
to contain functions with types in |Set|. This was necessary, since the standard library version of
|N-ary| can hold functions of arbitrary level (i.e. |Set n|), and therefore the level of the 
|N-ary| argument inside |ConstructorMapping| could not be inferred (since this depends on which function
one tries to store in that field), giving an unsolved constraint
which prevented the module from being imported without using the unsound type-in-type option.

Using this |N-ary| we can now define an entry in our mapping |Table| as having an arity, and mapping
a |Name| (which is Agda's internal representation of an identifier, see Fig.~\ref{fig:reflection}) to a
constructor in the AST we would like to cast the |Term| to.

\begin{code}
N-ary : (n : ℕ) → Set → Set → Set
N-ary zero    A B = B
N-ary (suc n) A B = A → N-ary n A B

_dollarn_ : ∀ {n} {A : Set} {B : Set} → N-ary n A B → (Vec A n → B)
f dollarn []       = f
f dollarn (x ∷ xs) = f x dollarn xs

data ConstructorMapping (astType : Set) : Set₁ where
  _\#_↦_       : (arity : ℕ)
               → Name
               → N-ary arity astType astType
               → ConstructorMapping astType

Table : Set → Set₁
Table a = ((ℕ → a) × List (ConstructorMapping a))

lookupName : {a : Set}      → List     (ConstructorMapping a)
                            → Name
                            → Maybe    (ConstructorMapping a)
lookupName [] name = nothing
lookupName (arity \# x ↦ x₁ ∷ tab) name with name ≟-Name x
lookupName (arity \# x ↦ x₁ ∷ tab) name | yes p = just (arity \# x ↦ x₁)
lookupName (arity \# x ↦ x₁ ∷ tab) name | no ¬p = lookupName tab name
\end{code}

With the above ingredients we can now define the function |convert| below, which, given a mapping of
type |Table a|, where $a$ is the type we would like to cast to, for example |Expr|, and a
|Term| obtained from one of Agda's reflection keywords, produces a value which might be a
properly converted term of type $a$. We also provide the helper function |lookupName|, which, given
a mapping and a |Name|, finds the corresponding entry in the mapping table. If nothing usable is found,
|nothing| is returned. 

An example of such a mapping would be the one required for our |Expr| example.

\begin{figure}[h]
\begin{code}
exprTable : Table Expr
exprTable = (Variable ,
             2   \# (quote _+_ )     ↦ Plus ∷
             0   \# (quote ℕ.zero)   ↦ Zero ∷
             1   \# (quote ℕ.suc )   ↦ Succ ∷ [])
\end{code}
\caption{The mapping for converting to the imaginary |Expr| AST. }\label{fig:exprTable}
\end{figure}

Here, we are saying that any variables encountered should be stored as |Variable| elements,
the |_+_| operator should be a |Plus| constructor (we are required to specify that it takes 2 arguments),
that a |zero|, from the |Data.Nat| standard library, should be treated as our |Zero| constructor, and
finally that |suc| translates to |Succ| and expects 1 argument.

The function that does this conversion for us looks like this. Note that it isn't intended to
be called directly; a convenience function |doConvert| is defined below. 

\ignore{
\begin{code}

data EqN : ℕ → ℕ → Set where
  yes : {m : ℕ} → EqN m m
  no  : {m n : ℕ} → EqN m n


≟-Nat-cong : (m : ℕ) → (n : ℕ) → EqN m n → EqN (suc m) (suc n)
≟-Nat-cong .n n yes = yes
≟-Nat-cong  m n no  = no


_≟-ℕ_ : (m : ℕ) → (n : ℕ) → EqN m n
zero ≟-ℕ zero = yes
zero ≟-ℕ suc n = no
suc m ≟-ℕ zero = no
suc m ≟-ℕ suc n = ≟-Nat-cong m n (m ≟-ℕ n)

\end{code}
}
\begin{code}
mutual
  convert : {a : Set} → Table a → Term → Maybe a
  convert (vc , tab) (var x args) = just (vc x)
  convert (vc , tab) (con c args) = appCons (vc , tab) c args
  convert (vc , tab) (def f args) = appCons (vc , tab) f args
  convert (vc , tab)     _        = nothing
\end{code}


If it encounters a variable, it just uses the constructor which stands for variables. Note that
the parameter is the de Bruijn-index of the variable, which might or might not be in-scope.
This is something to check for afterwards, if a |just| value is returned.

\textbf{\textsc{Note}}: This is also why one might need
an intermediary data structure to convert to, after which checks for invariants can be done. Typically,
it will not be possible to directly |convert| to some property-preserving data structure such
as |BoolExpr n| in one step; this will typically require post-processing.

In the case of a constructor or a definition applied to arguments, the function |appCons| is called,
which looks up a |Name| in the mapping and tries to recursively |convert| its arguments, then applies the given constructor to
these new arguments.

% the comment at the top of this code block fixes the indentation.
% indentation is forgotten over code blocks, it seems.
\begin{code}
-- mutual continues...
  appCons : {a : Set} → Table a → Name → List (Arg Term) → Maybe a
  appCons (vc , tab) name args with lookupName tab name
  appCons (vc , tab) name args | just (arity       \# x  ↦ x₁)   with convertArgs (vc , tab) args
  appCons (vc , tab) name args | just (arity       \# x₁ ↦ x₂)   | just x with length x ≟-ℕ arity
  appCons (vc , tab) name args | just (.(length x) \# x₁ ↦ x₂)   | just x | yes = just (x₂ dollarn fromList x)
  appCons (vc , tab) name args | just (arity       \# x₁ ↦ x₂)   | just x | no  = nothing
  appCons (vc , tab) name args | just (arity       \# x  ↦ x₁)   | nothing = nothing
  appCons (vc , tab) name args | nothing = nothing

  convertArgs : {a : Set} → Table a → List (Arg Term) → Maybe (List a)
  convertArgs tab [] = just []
  convertArgs tab (arg v r x ∷ ls) with convert tab x
  convertArgs tab (arg v r x ∷ ls) | just x₁ with convertArgs tab ls
  convertArgs tab (arg v r x ∷ ls) | just x₂ | just x₁ = just (x₂ ∷ x₁)
  convertArgs tab (arg v r x ∷ ls) | just x₁ | nothing = nothing
  convertArgs tab (arg v r x ∷ ls) | nothing = nothing
\end{code}

|appCons| and |convertArgs| just check to see if the desired |Name| is present in the provided
mapping, and if all the arguments, provided they are of the right number, also convert successfully. If
all this is true, the converted |Term| is returned as a |just e|, where $e$ is the new, converted member
of the AST. For example, see the unit tests in Fig. \ref{fig:test-autoquote}.

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

The module also exports the function |convertManages| and |doConvert|, which are to be used in the following
way.


\begin{figure}[h]
\begin{code}
something : {x y : ℕ}    → doConvert exprTable (quoteTerm ((1 + x + 2) + y))
                         ≡ Succ (Plus (Plus (Variable 1) (Succ (Succ Zero))) (Variable 0))
something = refl
\end{code}
\caption{Examples of |Autoquote| in use.}\label{fig:test-autoquote}
\end{figure}

Note the type signature of the |doConvert| function: we are implicitly assuming
that the conversion is successful (i.e. that it returns a |just| value). This 
allows a much cleaner implementation of the |convert| function; it can try all
the allowed constructors, and if none of them match, it can fail with a |nothing| value.
This is a lot simpler than writing a predicate function with the same pattern matching 
structure by hand, since sometimes the with-clauses are expanded unpredictably. The net effect
of writing a pair of functions in this style is the same as the ``usual'' way of writing a predicate
function by hand, in that a compile-time error is generated if the function |doConvert| is 
invoked on an argument with the wrong shape.


The |BoolExpr| AST used in \ref{sec:boolean-tautologies} provides a
good motivating example for using |Autoquote|, therefore a slightly
more real-world example of |Autoquote| in use can be found in
Sec.~\ref{sec:autoquote-example}.


\chapter{Proof by Reflection}
\label{sec:proof-by-reflection}

The idea behind proof by reflection is simple: given that type theory
is both a programming language and a proof system, it is possible to
define functions that compute proofs. Reflection is an overloaded word
in this context, since in programming language technology reflection
is the capability of converting some piece of concrete program syntax
into a syntax tree object which can be manipulated in the same
system. Reflection in the proof technical sense is the method of
mechanically constructing a proof of a theorem by inspecting its
shape.
Here we will present two case studies illustrating proof by
reflection and how Agda's reflection mechanism can make the technique
more usable and accessible.







\section{Simple Example: Evenness}\label{sec:evenness}

To illustrate the concept of proof by reflection, we will cover an example taken from
Chlipala~\cite{chlipala2011certified}, where we develop a procedure to automatically
prove that a number is even. We start by defining the
property |Even| below. There are two constructors: the first
constructor says that zero is even; the second constructor states that
if $n$ is even, then so is $2 + n$.

\begin{code}
data Even      : ℕ → Set where
  isEvenZ      :                          Even 0
  isEvenSS     : {n : ℕ} → Even n     →   Even (2 + n)
\end{code}

Using these rules to produce the proof that some large number |n| is
even can be very tedious: the proof that $2 \times n$ is even requires |n|
applications of the |isEvenSS| constructor. For example, here is the
proof that 6 is even:

\begin{code}
isEven6 : Even 6
isEven6 = isEvenSS (isEvenSS (isEvenSS isEvenZ))
\end{code}

To automate this, we will show how to \emph{compute} the proof
required. We start by defining a predicate |even?| that
returns the unit type when its input is even and bottom otherwise.
In this context |⊤| and |⊥| can be seen as the analogues of |true|
and |false|. The meaning of such a decision function is that there exists
a proof that some number is even, if it is |0| or |2 + n|. That is our
claim, at least. The idea
of ``there exists'' is perfectly modeled by the unit and empty types,
since the unit type has one inhabitant, the empty type none.

\begin{code}
even? : ℕ → Set
even? 0                 = ⊤
even? 1                 = ⊥
even? (suc (suc n))     = even? n
\end{code}


Next we need to show that the |even?| function is \emph{sound}, that
our claim holds. To do so, we prove that when |even? n| returns |⊤|,
the type |Even n| is
inhabited, and since we are working in a constructive logic, the only
way to show this is to give some witness. This is done in the function |soundnessEven|. What is
actually happening here is that we are giving a recipe for
constructing proof trees, such as the one we manually defined for
|isEven6|.

\begin{code}
soundnessEven : {n : ℕ} → even? n → Even n
soundnessEven {0}              tt        = isEvenZ
soundnessEven {1}              ()
soundnessEven {suc (suc n)}    s         = isEvenSS (soundnessEven s)
\end{code}

Note that in the case branch for 1, we do not need to provide a
right-hand side of the function definition. The assumption, |even?
1|, is uninhabited, and we discharge this branch using Agda's
absurd pattern ().

Now that this has been done, if we need a proof that some arbitrary
$n$ is even, we only need to instantiate |soundnessEven|. Note that
the value of $n$ is an implicit argument to |soundnessEven|. The only
argument we need to provide to our |soundnessEven| lemma is a proof
that |even? n| is inhabited. For any closed term, such as the numbers |28|
or |8772|, this proof obligation can be reduced to proving 
|⊤|, which is proven by the single constructor it has, |tt|.

\begin{code}
isEven28        : Even 28
isEven28        = soundnessEven tt

isEven8772      : Even 8772
isEven8772      = soundnessEven tt
\end{code}

Now we can easily get a proof that arbitrarily large numbers are even,
without having to explicitly write down a large proof tree. Note that
it's not possible to write something with type |Even 27|, or any other uneven
number, since the parameter |even? n| cannot be instantiated, thus
|tt| would not be accepted where it is in the |Even 28| example. This will
produce a |⊤ !=< ⊥| type error at compile-time.

Since the type |⊤| is a simple record type, Agda can infer the |tt|
argument, which means we can turn the assumption |even? n| into an
implicit argument, meaning a user could get away with writing just
|soundnessEven| as the proof, letting the inferrer do the rest. For
clarity this is not done here, but the complete implementation
available on github does use this trick. A detailed explanation of this
technique, which is used extensively in the final code, is given in
Sec.~\ref{sec:implicit-unit}.

\section{Second Example: Boolean Tautologies}\label{sec:boolean-tautologies}

Another application of the proof by reflection technique
is boolean expressions which are a tautology. We will follow the same
recipe as for even naturals, with one further addition. In the
previous example, the input of our decision procedure |even?| and the
problem domain were both natural numbers. As we shall see, this need
not always be the case.

Take as an example the boolean formula in equation \ref{eqn:tauto-example}.
\begin{align}\label{eqn:tauto-example}
(p_1 \vee q_1) \wedge (p_2 \vee q_2) \Rightarrow (q_1 \vee p_1) \wedge (q_2 \vee p_2)
\end{align}

It is trivial to see that this is a tautology, but proving this 
using deduction rules for booleans would be rather tedious. It
is even worse if we want to check if the formula always holds by
trying all possible variable assignments, since this will give $2^n$
cases, where $n$ is the number of variables.

To automate this process, we will follow a similar approach to
the one given in the section on even natural numbers (Sec.~\ref{sec:evenness}). We start by defining an
inductive data type to represent boolean expressions with $n$ free
variables in Fig.~\ref{fig:boolexprn}.

\begin{figure}[h]
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
\caption{Inductive definition of Boolean expressions having $n$ free variables.}\label{fig:boolexprn}
\end{figure}



There is nothing
surprising about this definition; we use the type |Fin n| to ensure
that variables (represented by |Atomic|) are always in scope. If we want to
evaluate the expression, however, we will need some way to map variables to values.
Enter |Env n|, it has fixed size $n$ since a |BoolExpr n| has $n$ free variables.

\begin{code}
Env   : ℕ → Set
Env   = Vec Bool
\end{code}

Now we can define our decision function, which decides if a given
boolean expression is true or not, under some assignment of variables. It does this by evaluating
the formula's AST. For example, |And| is converted to
the boolean function |_∧_|, and its two arguments in turn are
recursively interpreted.

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

Recall our decision function |even?| in the previous section. It returned
|⊤| if the proposition was valid, |⊥| otherwise. Looking at |⟦_⊢_⟧|, we see that
we should just translate |true| to the unit type and false to the empty type, to get
the analogue of the |even?| function.

We call this function |P|, the string parameter serving to give a clearer type error
to the user, if possible.

\begin{code}
data Error (e : String) : Set where

So   : String → Bool → Set
So   _        true     = ⊤
So   err      false    = Error err

P    : Bool → Set
P    = So "Argument expression does not evaluate to true."
\end{code}
\ignore{
\begin{code}
data Diff : ℕ → ℕ → Set where
  Base : ∀ {n}   → Diff n n
  Step : ∀ {n m} → Diff (suc n) m → Diff n m
\end{code}

\begin{code}
-- peels off all the outermost Pi constructors,
-- returning a term with freeVars free variables.

stripPi : Term → Term
stripPi (pi args (el s t)) = stripPi t
-- identity otherwise
stripPi (var x args) = var  x    args
stripPi (con c args) = con  c    args
stripPi (def f args) = def  f    args
stripPi (lam v σ t)  = lam  v σ  t
stripPi (sort x)     = sort x
stripPi unknown      = unknown

isSoExprQ : (t : Term) → Set
isSoExprQ (var x args) = ⊥
isSoExprQ (con c args) = ⊥
isSoExprQ (def f args) with Data.Nat._≟_ (length args) 2
isSoExprQ (def f args) | yes p with tt
isSoExprQ (def f [])                        | yes () | tt
isSoExprQ (def f (x ∷ []))                  | yes () | tt
isSoExprQ (def f (a ∷ arg v r x ∷ []))      | yes p  | tt with f ≟-Name quote So
isSoExprQ (def f (a ∷ arg v r x ∷ []))      | yes p₁ | tt | yes p = ⊤
isSoExprQ (def f (a ∷ arg v r x ∷ []))      | yes p  | tt | no ¬p = ⊥
isSoExprQ (def f (x ∷ x₃ ∷ x₄ ∷ args))      | yes () | tt
isSoExprQ (def f args)                      | no ¬p with tt
isSoExprQ (def f [])                        | no ¬p | tt = ⊥
isSoExprQ (def f (x ∷ xs))                  | no ¬p | tt = ⊥
isSoExprQ (lam v σ t)                       = ⊥
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
stripSo (lam v σ t)    ()
stripSo (pi t₁ t₂)   ()
stripSo (sort x)     ()
stripSo unknown      ()


isBoolExprQ' : (n : ℕ) → (t : Term) → Set
isBoolExprQ' n (var x args) with (1 + x) ≤? n
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
isBoolExprQ' n (lam v σ t) = ⊥
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
term2boolexpr n (var x args) pf with (1 + x) ≤? n
term2boolexpr n (var x args) pf | yes p = Atomic (fromℕ≤ {x} p)
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
term2boolexpr n (lam v σ t)  ()
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

zeroleast : (k n : ℕ) → Diff k (k + n)
zeroleast k zero    = coerceDiff (zeroId k) Base
zeroleast k (suc n) = Step (coerceDiff (succLemma k n) (zeroleast (1 + k) n))

\end{code}
}


Now that we have these helper functions, it is easy to define what it
means to be a tautology. We quantify over a few boolean variables, and
wrap the formula in our |P| decision function. If the resulting type is
inhabited, the argument to |P| is a tautology, i.e., for each
assignment of the free variables the entire equation still evaluates
to |true|. An example encoding of such a theorem is Figure \ref{fig:exampletheorem}.

One might wonder why propositions are not encoded in the slightly more 
intuitive propositional equality style, for example |(b : Bool) → b ∨ ¬ b ≡ true|, since
that notation more obviously reflects the meaning of ``being a tautology'', as opposed 
to one having to understand the |So| function. This is detailed in Sec.~\ref{sec:no-propositional-equality}.

\begin{figure}\label{fig:exampletheorem}
\begin{code}
exampletheorem : Set
exampletheorem = (p1 q1 p2 q2 : Bool)   →   P  (         (p1 ∨ q1) ∧ (p2 ∨ q2)
                                                   ⇒     (q1 ∨ p1) ∧ (q2 ∨ p2))
\end{code}
\caption{Example encoding of a tautology.}
\end{figure}

Here a complication arises, though. We are quantifying over a list of boolean values \emph{outside}
of the decision function |P|, so proving |P| to be sound will not suffice. We just defined a decision function (|⟦_⊢_⟧|)
to take an environment, an expression, and return a boolean. In Figure \ref{fig:exampletheorem}, though,
we effectively quantified over all possible environments. We are going to need a way
to lift our decision function to arbitrary environments.



The way we do this is the function |foralls|. This function represents the  analogue
of |even?| in this situation: it returns a type which is only inhabited if the argument boolean
expression is true under all variable assignments. This is done by generating a full binary tree
of unit values |⊤|, the single possible value which only exists if the interpretation function |⟦_⊢_⟧|
evaluates to |true| in every leaf. This corresponds precisely to $b$ being a tautology.

The |Diff| argument is unfortunately needed to prove that forallsAcc will eventually produce a
tree with depth equal to the number of free variables in an expression. 
\begin{code}
forallsAcc : {n m : ℕ} → BoolExpr m → Env n → Diff n m → Set
forallsAcc b acc    (Base     ) = P ⟦ acc ⊢ b ⟧
forallsAcc b acc    (Step y   ) =
  forallsAcc b (true ∷ acc) y × forallsAcc b (false ∷ acc) y

foralls : {n : ℕ} → BoolExpr n → Set
foralls {n} b = forallsAcc b [] (zeroleast 0 n)
\end{code}

Now we finally know our real decision function, we can set about proving its
soundness. Following the evens example, we want a function something like this.

\begin{spec}
sound : {n : ℕ} → (b : BoolExpr n) → foralls b → ...
\end{spec}
What should the return type of the |sound| lemma be? We would like to
prove that the argument |b| is a tautology, and hence, the |sound|
function should return something of the form |(b1 ... bn : Bool) -> P
B|, where |B| is an expression in the image of the interpretation
|⟦_⊢_⟧|. For instance, the statement |exampletheorem| is a proposition
of this form.

The function |proofObligation|, given a |BoolExpr n|, generates the
corresponding proof obligation. That is, it gives back the type which
should be equal to the theorem one wants to prove. It does this by
first introducing $m$ universally quantified boolean
variables. These variables are accumulated in an environment. Finally, when $m$
binders have been introduced, the |BoolExpr| is evaluated under this
environment.

Refer to Sec.~\pref{sec:explain-diff} for
a thorough explanation of the parameter |Diff n m| which, like here in |proofObligation|, is also passed into |forallsAcc|.

\begin{code}
proofObligation   : (n m : ℕ) → Diff n m → BoolExpr m → Env n → Set
proofObligation   .m   m    (Base    ) b acc = P ⟦ acc ⊢ b ⟧ 
proofObligation   n    m    (Step y  ) b acc =
  (a : Bool) →
      proofObligation (1 + n) m y b (a ∷ acc)
\end{code}

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
}

Now that we can interpret a |BoolExpr n| as a theorem using |proofObligation|, and we have a
way to decide if something is true for a given environment, we still
need to show the soundness of our decision function |foralls|. That is, we need
to be able to show that a formula is true if it holds for every
possible assignment of its variables to |true| or |false|.






\begin{code}
soundnessAcc :   {m : ℕ} →          (b : BoolExpr m) →
                 {n : ℕ} →          (env : Env n) →
                 (d : Diff n m) →   forallsAcc b env d →
                 proofObligation n m d b env
soundnessAcc     bexp     env Base     H with ⟦ env ⊢ bexp ⟧
soundnessAcc     bexp     env Base     H | true  = H
soundnessAcc     bexp     env Base     H | false = Error-elim H
soundnessAcc {m} bexp {n} env (Step y) H =
  λ a → if {λ b → proofObligation (1 + n) m y bexp (b ∷ env)} a
    (soundnessAcc bexp (true  ∷ env)    y (proj₁ H))
    (soundnessAcc bexp (false ∷ env)    y (proj₂ H))
\end{code}

\begin{code}
soundness       : {n : ℕ} → (b : BoolExpr n) → foralls b
                → proofObligation 0 n (zeroleast 0 n) b []
soundness {n} b i = soundnessAcc b [] (zeroleast 0 n) i
\end{code}
If we look closely at the definition of |soundnessAcc| (which is
where the work is done -- |soundness| merely calls
|soundnessAcc| with some initial input, namely the |BoolExpr n|, an
empty environment, and the proof
that |soundnessAcc| will be called ($n-0$) times, resulting in an environment
of size $n$ everywhere the expression is to be evaluated --
we see that we build up a function
that, when called with the values assigned to the free variables,
builds up the environment and eventually returns the
leaf from |foralls| which is the proof that the formula is a tautology
in that specific case.

Now, we can prove theorems by calling |soundness b p|, where |b| is the
representation of the formula under consideration, and |p| is the evidence
that all branches of the proof tree are true. Agda is convinced
that the representation does in fact correspond to the concrete
formula, and also that |soundness| gives a valid proof. In fact, we need not
even give |p| explicitly; since the only valid values of |p| are pairs of |tt|,
the argument can be inferred automatically, if it is inhabited.

If the module
passes the type checker, we know our formula is both a tautology, and
that we have the corresponding proof object at our disposal
afterwards, as in the following example.


\begin{code}
rep          : BoolExpr 2
rep          = Imp (And (Atomic (suc zero)) (Atomic zero)) (Atomic zero)

someTauto    : (p q : Bool)         → P( p ∧ q ⇒ q )
someTauto    = soundness rep _
\end{code}

The only part we still have to do manually is to convert the concrete
Agda representation (|p ∧ q ⇒ q|, in this case) into our abstract
syntax (|rep| here). This is unfortunate, as we end up typing out the
formula twice. We also have to count the number of variables
ourselves and convert them the to De Bruijn indices. This is
error-prone given how cluttered the abstract representation can get
for formulae containing many variables. It would be desirable for this
process to be automated. In Sec.~\ref{sec:addrefl} a solution is
presented using Agda's recent reflection API.

\subsection{Why Not Propositional Equality?}\label{sec:no-propositional-equality}

The question of why the |So| operator is used here to denote that a formula is 
a tautology, as opposed to just writing the literal definition of tautology, namely
|∀ (b : Bool) → Q(b) ≡ true| for some formula |Q| depending on |b|, was posed in the previous section.
The reason for this is mainly a technical one. It is possible to prove tautologies of this form, but
using this format for reasoning about Boolean formulae becomes rather more involved.

The reason for this is
that the |So| operator returns a type, namely either unit or empty, which can
be passed around as an automatically-inferred implicit value (see Sec.~\ref{sec:implicit-unit} for a 
detailed explanation about implicit inferred arguments), removing the need to put |refl| everywhere
such a proof is needed -- a unit or pair type can be inferred if it exists\footnote{Compare the example
implementation of a ring solver in Agda, which has |refl|s all over the place \cite{ringsolver}, which
cannot be made implicit and thus omitted.}. Because of this, the
recursive cases of functions such as |soundness| become a lot simpler: the interpretation
of a sub-expression being true becomes the same as a unit type being inhabited, and the and-operator
corresponds to a pair. If the propositional equality way was being used, many lemmas such as that 
|a ∧ b ≡ true ⇒ a ≡ true ∧ b ≡ true| need to be proven, and they are continually needed to
pull apart such propositions for recursive calls. Using an existential type is much simpler in this
case.
% proof irrelevance: prove a type with a program, but then throw away the program, i.e. the actual proof doesn't matter??

\subsection{Why Not Enumerate Environments?}\label{sec:no-enumerate-environments}


One of the reasons for not enumerating environments (|∀ (e : Env n) → P( someprop )|) is that
referring to variables becomes a bit of a problem. One would have to introduce some new syntax, such as a constructor
|Var : Fin n → Bool| which could be used to refer to an element of the environment by number. This is 
rather less elegant than the current implementation, where one simply brings a few Boolean variables into scope in
the native Agda manner, using a telescope (i.e. |(p q r : Bool) → P(p ∧ q ⇒ r)|). This has another advantage, namely
that if one writes down a proposition, one is forced to only use valid variables, which translate to in-scope de Bruijn indices.

Another difficulty of enumerating over environments is the generation of the proof obligation. Currently, a telescope
can be generated easily via recursion (see the function |proofObligation|), as opposed to having to generate all possible 
lists. Some investigation was done to try and show that environments (lists of Booleans) of length $n$ are enumerable,
but the results were not as elegant as those presented in Sec.~\ref{sec:boolean-tautologies}. Also, generating the environments by quantifying over
fresh variables and adding them to an accumulating environment saves creating a large binary tree with all the possible
environments in the leaves.

\subsection{What Is This |Diff| You Speak Of?}\label{sec:explain-diff}

Back in Sec.~\ref{sec:boolean-tautologies} the function |proofObligation| (among others)
had a parameter of type |Diff n m|. Recalling the function's
definition, note that there are two variables, $n$ and $m$ giving the size of the environment
and the maximum number of bound variables in the proposition, respectively. 

\begin{spec}
proofObligation   : (n m : ℕ) → Diff n m → BoolExpr m → Env n → Set
proofObligation   .m   m    (Base    ) b acc = P ⟦ acc ⊢ b ⟧ 
proofObligation   n    m    (Step y  ) b acc =
  (a : Bool) →
      proofObligation (1 + n) m y b (a ∷ acc)
\end{spec}

This cannot be 
right, since our interpretation function |⟦_⊢_⟧| requires that these $m$ and $n$ are equal.
We cannot, however, make them equal in the type signature for |proofObligation|, since we are 
building up the environment with an accumulating parameter. Because of this, we introduce |Diff|.


\begin{figure}[h]
\begin{spec}
data Diff : ℕ → ℕ → Set where
  Base : ∀ {n}   → Diff n n
  Step : ∀ {n m} → Diff (suc n) m → Diff n m
\end{spec}
\caption{The definition of |Diff|}\label{fig:diff-datatype}
\end{figure}

The |Diff| data type is defined as in Fig.~\ref{fig:diff-datatype}, and was necessary 
because given a term of type |BoolExpr m|, being a proposition with at most $m$ 
variables, it should be ensured that in the end an environment of size $m$ would be produced.
The necessity of $m \equiv n$ is obvious considering that the evaluation function needs to
be able to look up the variables in the Boolean expression, but being a recursive function
which introduces a new variable to the telescope one at a time, we need some way to ``promise''
that in the end $m$ will be equal to $n$. As can be seen in the definition of the |Base| constructor,
this is exactly what is happening.

The same thing is necessary in the functions |forallsAcc| and 
friends, given that they also recursively construct or look up proofs that need to have a corresponding
size to the |BoolExpr|, but given that they use the same technique in a slightly less overt manner
they are not separately detailed here.



\section{Adding Reflection}\label{sec:addrefl}

We can get rid of the aforementioned duplication using Agda's reflection API. More
specifically, we will use the |quoteGoal| keyword to inspect the
current goal. Given the |Term| representation of the goal, we can
convert it to its corresponding |BoolExpr|.

The conversion between a |Term| and |BoolExpr| is achieved using the
|concrete2abstract| function:
\begin{code}
concrete2abstract    :     (t     : Term)        → (n : ℕ)
                     →     {pf    : isSoExprQ (stripPi t)}
                     →     {pf2   : isBoolExprQ n (stripPi t) pf}
                     →     BoolExpr n
\end{code}
\ignore{
\begin{code}
concrete2abstract t n {pf} {pf2} = term2boolexpr n (stripSo (stripPi t) pf) pf2
\end{code}}\!\!
Note that not every |Term| can be converted to a |BoolExpr|. The
|concrete2abstract| function requires additional assumptions about the
|Term|: it should only contain functions such as |_∧_| or |_∨_|, and
bound variables. This is ensured by the assumptions
|isBoolExprQ| and friends.

The |concrete2abstract| function is rather verbose, and is mostly omitted.
A representative snippet is given in Fig. \pref{fig:concrete2abstract}. The attentive reader will notice that
the function in the referenced figure is called |term2boolexpr|; this is because we also unwrap the outermost call to |P| 
and the telescope quantifying over (introducing) the variables before doing the conversion, since these elements are unnecessary in the |BoolExpr| representation. 
This can be seen as a helper function to |concrete2abstract| where the ``interesting'' (if you happen to be a flagellant) work happens.
The functions |isBoolExprQ|
and |isSoExprQ| simply traverse the |Term| to see if it fulfills the requirements of
being a boolean expression preceded by a series of universally quantified boolean variables, enclosed in a
call to |P|.

\begin{figure}
\begin{spec}
term2boolexpr n (con tf []) pf with tf ≟-Name quote true
term2boolexpr n (con tf []) pf | yes p = Truth
...
term2boolexpr n (def f []) ()
term2boolexpr n (def f (arg v r x ∷ [])) pf with f ≟-Name quote ¬_
term2boolexpr n (def f (arg v r x ∷ [])) pf | yes p = Not (term2boolexpr n x pf)
...
term2boolexpr n (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) pf | no ¬p with f ≟-Name quote _∧_
...
\end{spec}
\caption{An illustration of converting a |Term| into a |BoolExpr|.}\label{fig:concrete2abstract}
\end{figure}


All these pieces are assembled in the |proveTautology| function.

\ignore{
\begin{code}
freeVars : Term → ℕ
freeVars (pi (arg visible relevant (el (lit _) (def Bool []))) (el s t)) = 1 + (freeVars t)
-- identity otherwise
freeVars    _         = 0
\end{code}
}
\begin{code}
proveTautology :    (t     : Term) →
                    {pf    : isSoExprQ (stripPi t)} →
                    let n = freeVars t in
                        {pf2   : isBoolExprQ n (stripPi t) pf} →
                        let b = concrete2abstract t n {pf} {pf2} in
                            {i : foralls b} →
                            proofObligation 0 n (zeroleast 0 n) b []
proveTautology t {_}{_}{i} = 
  soundness (concrete2abstract t (freeVars t)) i
\end{code}
The |proveTautology| function converts a raw |Term| to a |BoolExpr n|
format and calls the |soundness| lemma. It uses a few auxiliary
functions such as |freeVars|, which counts the number of variables
(needed to be able to instantiate the $n$ in |BoolExpr n|), and
|stripSo| \& |stripPi|, which peel off the universal quantifiers and the
function |So| with which we wrap our tautologies. These helper
functions have been ommitted for brevity, since they are rather
cumbersome and add little to the understanding of the subject at
hand.


These are all the ingredients required to automatically prove that
formulae are tautologies.  The following code illustrates the use of
the |proveTautology| functions; we can omit the implicit arguments for
the reasons outlined in Sec.~\ref{sec:implicit-unit}.

\begin{code}
exclMid    : (b : Bool) → P(b ∨ ¬ b)
exclMid    = quoteGoal e in proveTautology e

peirce     : (p q : Bool) → P(((p ⇒ q) ⇒ p) ⇒ p)
peirce     = quoteGoal e in proveTautology e

fave       : exampletheorem -- defined in Fig.~\ref{fig:exampletheorem}
fave       = quoteGoal e in proveTautology e
\end{code}


This shows that the reflection capabilities recently added to Agda are quite useful for
automating certain tedious tasks, since the programmer now need not encode the boolean expression
twice in a slightly different format. The conversion now happens automatically, without loss
of expressive power or general applicability of the proofs resulting from |soundness|.
Furthermore, by using the proof by reflection technique, the proof is generated automatically.

\subsection{An Aside: Real-world Example of |Autoquote|}\label{sec:autoquote-example}

The process of quoting to a |BoolExpr n| outlined in Sec.~\ref{sec:addrefl}
quickly becomes an ugly mess, with functions checking properties of an expression (such
as only certain functions occurring) being pretty similar, save the number of arguments
functions require or which functions are allowed.

The actual conversion function also ends up having many branches, checking if the current
constructor or definition is on we know, \&c. This process can be made a lot less ugly.
Recall the |Autoquote| module developed in
Sec.~\ref{sec:autoquote}; this can be used here, both as an
illustration of the use of |Autoquote|, and to avoid code duplication,
thus making the code for |term2boolexpr| more concise.

|Autoquote| only supports simple recursive data types, so the first problem we encounter is that
|BoolExpr n| has an argument of type |Fin n| to its constructor |Atomic| (see Fig.~\ref{fig:boolexprn}).
Because of this, we introduce a simpler, intermediary data structure, to which we will convert
from |Term|. This type, called |BoolInter|, is presented in Fig. \ref{fig:boolinter}.

\begin{figure}[h]
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
\caption{An intermediary data type, which is a simplified (constraint-free) version of |BoolExpr|.}\label{fig:boolinter}
\end{figure}

The mapping needed for |Autoquote| is as follows: we mention which constructor represents
de Bruijn-indexed variables and what the arity is of the different constructors. This way
only |Term|s with and, or, not, true or false are accepted. Using this mapping, we can construct
the function |term2boolexpr'| which, for suitable |Term|s, gives us an expression in |BoolInter|. 

\begin{code}
boolTable : Table BoolInter
boolTable = (Atomic ,
                  2 \# (quote _∧_  ) ↦ And
            ∷     2 \# (quote _∨_  ) ↦ Or
            ∷     1 \# (quote  ¬_  ) ↦ Not
            ∷     0 \# (quote true ) ↦ Truth
            ∷     0 \# (quote false) ↦ Falsehood
            ∷     2 \# (quote _⇒_  ) ↦ Imp ∷ [])

term2boolexpr' : (t : Term) → {pf : convertManages boolTable t} → BoolInter
term2boolexpr' t {pf} = doConvert boolTable t {pf}
\end{code}

Once we have a |BoolInter| expression, we just need to check that its
variables are all in-scope (this means that $\forall$ |Atomic x| $ : x < n$, if we
want to convert to a |BoolExpr n|). This is done in |bool2fin|, assuming that |bool2finCheck|
holds (the latter simple expresses the aforementioned in-scope property).

\ignore{
\begin{code}
bool2finCheck : (n : ℕ) → (t : BoolInter) → Set
bool2finCheck n Truth        = ⊤
bool2finCheck n Falsehood    = ⊤
bool2finCheck n (And t t₁)   = bool2finCheck n t × bool2finCheck n t₁
bool2finCheck n (Or t t₁)    = bool2finCheck n t × bool2finCheck n t₁
bool2finCheck n (Not t)      = bool2finCheck n t
bool2finCheck n (Imp t t₁)   = bool2finCheck n t × bool2finCheck n t₁
bool2finCheck n (Atomic x)   with suc x ≤? n
bool2finCheck n (Atomic x)   | yes p = ⊤
bool2finCheck n (Atomic x)   | no ¬p = ⊥

bool2fin : (n : ℕ) → (t : BoolInter) → (bool2finCheck n t) → BoolExpr n
bool2fin n Truth       pf          = Truth
bool2fin n Falsehood   pf          = Falsehood
bool2fin n (And t t₁) (p₁ , p₂)    = And (bool2fin n t p₁) (bool2fin n t₁ p₂)
bool2fin n (Or t t₁)  (p₁ , p₂)    = Or  (bool2fin n t p₁) (bool2fin n t₁ p₂)
bool2fin n (Not t)     p₁          = Not (bool2fin n t p₁)
bool2fin n (Imp t t₁) (p₁ , p₂)    = Imp (bool2fin n t p₁) (bool2fin n t₁ p₂)
bool2fin n (Atomic x)  p₁ with suc x ≤? n
bool2fin n (Atomic x)  p₁ | yes p  = Atomic (fromℕ≤ {x} p)
bool2fin n (Atomic x)  () | no ¬p
\end{code}
}
\begin{spec}
bool2finCheck : (n : ℕ) → (t : BoolInter) → Set
bool2finCheck n Truth        = ⊤
bool2finCheck n (And t t₁)   = bool2finCheck n t × bool2finCheck n t₁
...
bool2finCheck n (Atomic x)   with suc x ≤? n
bool2finCheck n (Atomic x)   | yes p    = ⊤
bool2finCheck n (Atomic x)   | no ¬p    = ⊥

bool2fin : (n : ℕ) → (t : BoolInter) → (bool2finCheck n t) → BoolExpr n
bool2fin n Truth       pf = Truth
bool2fin n (And t t₁) (p₁ , p₂) = And (bool2fin n t p₁) (bool2fin n t₁ p₂)
...
bool2fin n (Atomic x)  p₁ with suc x ≤? n
bool2fin n (Atomic x)  p₁ | yes p = Atomic (fromℕ≤ {x} p)
bool2fin n (Atomic x)  () | no ¬p
\end{spec}

With these ingredients, our |concrete2abstract| function presented in Sec.~\ref{sec:addrefl}
can be rewritten to the following  drop-in replacement, illustrating how useful such an
abstraction can be. 

\begin{spec}
concrete2abstract :
         (t : Term)
       → {pf : isSoExprQ (stripPi t)}
       → let t' = stripSo (stripPi t) pf in
            {pf2 : convertManages boolTable t'}
          → (bool2finCheck (freeVars t) (term2boolexpr' t' {pf2}))
          → BoolExpr (freeVars t)
concrete2abstract t {pf} {pf2} fin = bool2fin     (freeVars t)
                                                  (term2boolexpr'
                                                    (stripSo (stripPi t) pf)
                                                    {pf2})
                                                  fin
\end{spec}

This example illustrates how the |Autoquote| module can save a lot
of repetitive coding for converting an Agda |Term| into some invariant-preserving
AST such as |BoolExpr n|. 



\chapter{Type-safe Metaprogramming}\label{sec:type-safe-metaprogramming}

Another area in which an application for the new reflection API was found is that
of type-safe metaprogramming, taking advantage of Agda's very powerful type system.

Metaprogramming is a technique which is already widely used, for example in the LISP
community, and involves converting terms in the concrete syntax of a
programming language into an abstract syntax tree which can be
inspected and/or manipulated, and possibly be
made
concrete again, and thus can be evaluated as if it were code the
programmer had directly entered into a source file. In Agda the reflection happens at
compile-time, allowing for the strong static typing we have come to know and love.
If run-time reflection were possible, any program compiled with Agda would need to
include the complete typing system, a problem which doesn't exist in, for example,
Lisp, since it is dynamically typed, which makes run-time reflection possible. Here, therefore,
a compromise of sorts is required.

Reflection is well-supported and widely used in LISP and more
recently in Haskell, using the Template Haskell compiler
extension\cite{template-haskell}. It has enabled many time-saving
automations of tasks otherwise requiring
\emph{boilerplate}\footnote{According to the Oxford English
  Dictionary, boilerplate is defined as \emph{``standardized pieces of
    text for use as clauses in contracts or as part of a computer
    program''}.} code, such as automatically generating
embedding-projection function pairs for generic programming (for
example in \cite{norell2004prototyping}).


Clearly, the technique is a very useful one, but it does have a glaring
limitation (or should we say, potential pitfall), namely that when one
is developing a piece of Template Haskell code which
should generate some function, it often happens that one ends up
debugging type errors in the produced (machine-generated) code. This
is a tedious and painful process, since typically generated code is
much less self-explanatory or readable than human-written code.

Here we propose a new way of looking at metaprogramming, namely
type-safe metaprogramming. It would be great if one could define some
data structure for, say, lambda calculus, and have the guarantee that
any term constructed in this AST is type-correct. The obvious
advantage is then that the compiler will show up errors in whichever
method tries to build an invalid piece of abstract syntax at compile time, as opposed
to giving an obscure error pointing at some generated code, leaving
the programmer to figure out how to solve the problem.

In this section we will explore how one can leverage the power of
dependent types when metaprogramming.

\section{Example: Type-checking $\lambda$-calculus}

For the running example in this section, we will look at a
simply-typed lambda calculus (STLC) with type and scoping rules as
in Fig. \ref{fig:lambda-rules}. 
All the modules that deal with well-typed lambda expressions (everything in the |Metaprogramming| namespace
of the repository) are parameterised with a number of elements. A user of this
library should provide the following elements.

\begin{code}


\end{code}

\begin{itemize}
\item |U : Set| A data type representing your own universe. It might have such elements as |Nat| and |Bl| which might stand for natural numbers and boolean values.
\item |?type : U → Name| A function which, given an element of your universe, gives back the concrete Agda identifier which it stands for, such as |quote ℕ|.
\item |Uel : U → Set| An interpretation function, which returns the Agda type corresponding to some element of your universe.
\item |quoteBack : (x : U) → Uel x → Term| A function which can turn a value in your universe into an Agda |Term|
\item |equal? : (x : U) → (y : U) → Equal? x y| A function which implements decidable equality between elements of your universe.
\item |returnType : U| The return type for a CPS transformed function. Will be detailed in Sec.~\ref{sec:cps}.
\item |type? : Name → Maybe U| A function which translates Agda identifiers into elements of your universe |U|.
\item |quoteVal : (x : U) → Term → Uel x| Finally, a function which, given an Agda term, translates it into your universe.
\end{itemize}


The universe (set of possible types) we
use is |U'|, which is made up of base types (|O|) and function types (|_=>_|). There
is also an extra constructor |Cont| which stands for the type of a continuation. This will
be explained in the section on continuation-passing style, Sec.~\ref{sec:cps}.


\todo{ insert typing derivations here.}


As usual, these typing judgments (or derivations) translate naturally into
Agda syntax. This translation has been done in Fig. \ref{fig:stlc}.

The |WT| data type represents well-typed and closed (thus well-scoped)
simply-typed lambda calculus terms. Notice that type-incorrect terms cannot be instantiated, since
the dependent type signatures of the constructors allow us to express
constraints such as that a de Bruijn-indexed variable must be at most
$n$, with $n$ the depth of the current sub-expression, with depth
defined as the number of $\lambda$'s before one is at top-level
scope. We assume the reader to be familiar with nameless de Bruijn notation for 
lambda calculus (see \cite{de1972lambda}), i.e. the term $\lambda x . x$ is represented
as $\lambda . 0$.


\begin{code}
-- equality of types.
data Equal? {A : Set} : A → A → Set where
  yes  : forall {τ}     → Equal? τ τ
  no   : forall {σ τ}   → Equal? σ τ

-- ugh, this may not be in a parameterised module. if it is, such as
-- where it was in CPS.Apply, if you import CPS as CPS' = CPS . . . e.g.
-- then there's a panic, since quote Apply returns CPS.Apply, and all of
-- a sudden the number of arguments is invalid (i.e. the module arguments
-- are missing). ugh.
Apply : {A B : Set} → (A → B) → A → B
Apply {A} {B} x y = x y

\end{code}




For example, the arguments might look like this %todo less ugly wording

\begin{code}

---------
--- THIS STUFF may not be used other than as a parameter to the module.

data U : Set where
  Nat : U


?type : U → Name
?type r = quote ℕ

Uel : U → Set
Uel r = ℕ


quoteBack : (x : U) → Uel x → Term
quoteBack Nat zero    = con (quote ℕ.zero) []
quoteBack Nat (suc x) = con (quote ℕ.suc) (arg visible relevant (quoteBack Nat x) ∷ [])

equal? : (x : U) → (y : U) → Equal? x y
equal? Nat Nat = yes

ReturnType : U
ReturnType = Nat

type? : Name → Maybe U
type? n with n ≟-Name (quote ℕ.suc)
type? n | yes p = just Nat
type? n | no ¬p with n ≟-Name (quote ℕ.zero)
type? n | no ¬p | yes p = just Nat
type? n | no ¬p₁ | no ¬p with n ≟-Name (quote ℕ)
type? n | no ¬p₁ | no ¬p | yes p = just Nat
type? n | no ¬p₂ | no ¬p₁ | no ¬p = nothing

quoteVal : (x : U) → Term → Uel x
quoteVal Nat (var x args) = 0
quoteVal Nat (con c args) with c ≟-Name quote ℕ.zero
quoteVal Nat (con c args) | yes p = 0
quoteVal Nat (con c args) | no ¬p with c ≟-Name quote ℕ.suc
quoteVal Nat (con c []) | no ¬p | yes p = 0
quoteVal Nat (con c (arg v r x ∷ args)) | no ¬p | yes p = 1 + quoteVal Nat x
quoteVal Nat (con c args) | no ¬p₁ | no ¬p = 0
quoteVal Nat      _       = 0

-- result type.

-- end THIS STUFF
------------------------


\end{code}



Another constraint expressed is that an application can only be
introduced if both sub-expressions have reasonable types. Reasonable
in this context means that the function being applied must take an
argument of the type of the to-be-applied sub-expression.


\begin{figure}[h]
\begin{code}
data U' : Set where
  O       : U             → U'
  _=>_    : U'    → U'    → U'
  Cont    : U'            → U'
  
Ctx : Set
Ctx = List U'

data _∈'_ {A : Set} (x : A) : List A → Set where
  here    : {xs : List A}                        → x ∈' x ∷ xs
  there   : {xs : List A} {y : A} → x ∈' xs       → x ∈' y ∷ xs
  
data WT : (Γ : Ctx) → U' -> Set where
  Var   : ∀ {Γ} {τ}     → τ ∈' Γ                      → WT Γ τ
  _⟨_⟩  : ∀ {Γ} {σ τ}   → WT Γ (σ => τ) → WT Γ σ      → WT Γ τ
  Lam   : ∀ {Γ} σ {τ}   → WT (σ ∷ Γ) τ                → WT Γ (σ => τ)
  Lit   : ∀ {Γ} {x}     → Uel x                       → WT Γ (O x)
\end{code}
\caption{The data type modeling well-typed, well-scoped lambda calculus.}\label{fig:stlc}
\end{figure}
\ignore{
\begin{code}
infixl 30 _⟨_⟩ 
infixr 20 _=>_
infix 3 _∈'_
\end{code}
}

Note that the argument to |Var| is not an integral index, as one might expect, but a proof
that the variable points to a reasonable spot in the context. This proof is encoded in the |_∈_|
data structure, and is a semantically-extended index, in that the value in the list that is being
pointed at is stored along with the pointer. Thus, an index is recoverable from this structure, which
is useful if one wants to cast back to a true de Bruijn representation of a given lambda term. 

The |Ctx| type is simply our context for variables (mapping variables
to their type): it is defined as |List U'|, where the position in the list corresponds
to the de Bruijn-index of a variable. Since all terms are required to be well-scoped,
this makes sense, since each time a lambda-abstraction is introduced, the type of the 
variable to be bound at that point is consed onto the environment. This way, variables 
which are bound ``further away'' (in the de Bruijn-index sense) are nearer to the back of the list.

The following illustration should make this idea clearer.

... insert illustration here where variables are put on the ``stack''...

Now that we have this well-typed, well-scoped lambda language defined in Agda,
we can construct terms by hand which are well-formed by construction. The idea, though,
is to be able to do this automatically, using |quoteTerm|. This implies that
we need to write a function which converts |Term|s into a value of type |WT .. ..|. 
Constructing this |WT| term requires annotating the elements with types, but 
as it stands at the time of this writing, Agda returns untyped
terms. Therefore, the Agda compiler had to be modified for this work
to be feasible, since without type annotations, 
 type inference is necessary to determine the types of sub-expressions (especially of applications (e.g. |f ⟨ x ⟩ |), since we are basically 
free to introduce the type of the argument expression, $x$ in the example), which is why
unification of type variables is normally necessary. %TODO explain this properly
It is not impossible to implement a type inferencer in Agda (for example using Algorithm
W), %TODO reference algo W + possible implementations in Agda
but it is outside of the scope of this project. Additionally, this would require the
implementation of a type unification algorithm, and a total, structurally recursive (so as
to pass Agda's termination checker) unification algorithm is rather complex to implement \cite{mcbride2003first}.

Therefore the Agda compiler was modified to extend the internal data structure representing
|Term|s with a field on lambda abstractions, representing the type of their arguments. The precise
modifications to the compiler are detailed in Appendix \ref{sec:annotating-lambdas}.

Now that we have annotations in |Term|s, all that remains is to
type-check them and simultaneously convert them into |WT| terms. The
algorithm used here is inspired by the Agda tutorial written by Norell
\cite{Norell:2009:DTP:1481861.1481862}. The function |term2raw| first converts terms which are
actually lambda expressions (as opposed to, say, boolean expressions)
into an intermediary datatype, |Raw|, which can express all lambda
terms.

\begin{code}
data Raw : Set where
  Var  : ℕ              → Raw
  App  : Raw   → Raw    → Raw
  Lam  : U'    → Raw    → Raw
  Lit  : (x : U)   →  Uel x → Raw
\end{code}

Next we define the erasure of types and a view on terms which tells us if a term is
well-typed or not, and if it is, gives us the representation in |WT|.


\ignore{
\begin{code}

index : {A : Set} {x : A} {xs : List A} → x ∈' xs → ℕ
index   here    = zero
index (there h) = suc (index h)

data Lookup {A : Set} (xs : List A) : ℕ → Set where
  inside   : (x : A) (p : x ∈' xs) → Lookup xs (index p)
  outside  : (m : ℕ) → Lookup xs (length xs + m)

  
_!_ : {A : Set} (xs : List A) (n : ℕ) → Lookup xs n
[]        ! n      = outside n
(x ∷ x₁)  ! zero   = inside x here
(x ∷ x₁)  ! suc n with x₁ ! n
(x₂ ∷ x₁) ! suc .(index p)       | inside x p  = inside x (there p)
(x ∷ x₁)  ! suc .(length x₁ + m) | outside  m  = outside m

_=?=_ : (σ τ : U') → Equal? σ τ
O x          =?= O  y       with (equal? x y)
O .y         =?= O y  | yes = yes
O x          =?= O y  | no  = no
-- O          =?= O        = yes
O x          =?= (_ => _)   = no
(σ => τ)     =?= O  y       = no
(σ₁ => τ₁)   =?= (σ₂ => τ₂) with σ₁ =?= σ₂ | τ₁ =?= τ₂
(.σ₂ => .τ₂) =?= (σ₂ => τ₂) | yes | yes = yes
(.σ₂ => τ₁)  =?= (σ₂ => τ₂) | yes | no  = no
(σ₁ => .τ₂)  =?= (σ₂ => τ₂) | no  | yes = no
(σ₁ => τ₁)   =?= (σ₂ => τ₂) | no  | no  = no
O x          =?= Cont b     = no
(a => a₁)    =?= Cont b     = no
Cont a       =?= O y        = no
Cont a       =?= (b => b₁)  = no
Cont a       =?= Cont b     with a =?= b
Cont .b      =?= Cont b     | yes = yes
Cont a       =?= Cont b     | no  = no

\end{code}
}

\begin{code}
erase : forall {Γ τ} → WT Γ τ → Raw
erase (Var inpf)      = Var (index inpf)
erase (t ⟨ t₁ ⟩)      = App (erase t) (erase t₁)
erase (Lam σ t)       = Lam σ (erase t)
erase (Lit {_}{σ} x)  = Lit σ x

data Infer (Γ : Ctx) : Raw → Set where
  ok    : (τ : U') (t : WT Γ τ)  → Infer Γ (erase t)
  bad   : {e : Raw}              → Infer Γ e
\end{code}

Using this, we can assemble the various parts. For brevity, the function |term2raw| is omitted, but
it is very much comparable to the function which converts a |Term| into a |BoolExpr| (see Sec.~\ref{sec:boolexpr}). One
might reasonably ask why then |Autoquote| was not used, but |Autoquote| is most suited to simple inductive
data types without abstractions (eg. the definition of a simple |List| in Haskell).

Now we can write the actual type checking function, |infer|.  For variables and constants, the types are easy to deduce.


\begin{code}
infer : (Γ : Ctx)(e : Raw) → Infer Γ e
infer Γ (Lit ty x) = ok (O ty) (Lit {_}{ty} x)
infer Γ (Var x) with Γ ! x
infer Γ (Var .(index p))      | inside σ p = ok σ (Var p)
infer Γ (Var .(length Γ + m)) | outside m = bad
\end{code}

The lambda case is also not so complicated: a type $\sigma$ is added to the 
environment-stack, where $\sigma$ is the type of the argument to the lambda, and the body is type-checked with this new environment,
and if the body correctly type-checks with type $\tau$, we can return $\sigma \Rightarrow \tau$ as the type of the 
expression.

\begin{code}
infer Γ (Lam σ e) with infer (σ ∷ Γ) e
infer Γ (Lam σ .(erase t)) | ok τ t = ok (σ => τ) (Lam σ t)
infer Γ (Lam σ e) | bad = bad
\end{code}

The case for an application is a little trickier, since we must first check that the LHS
has a function type, and if so, check the type of the RHS, and finally verify that the type
of the RHS matches the domain of the function type.  If all this holds,  we have a valid application.
\begin{code}
infer Γ (App e e₁) with infer Γ e
infer Γ (App .(erase t) e₁) | ok (Cont a) t = bad
infer Γ (App .(erase t) e₁) | ok (O x) t = bad
infer Γ (App .(erase t) e₁) | ok (τ => τ₁) t with infer Γ e₁
infer Γ (App .(erase t₁) .(erase t₂)) | ok (σ => τ) t₁   | ok σ' t₂ with σ =?= σ'
infer Γ (App .(erase t₁) .(erase t₂)) | ok (.σ' => τ) t₁ | ok σ' t₂ | yes = ok τ (t₁ ⟨ t₂ ⟩ )
infer Γ (App .(erase t₁) .(erase t₂)) | ok (σ => τ) t₁   | ok σ' t₂ | no = bad
infer Γ (App .(erase t) e₁) | ok (τ => τ₁) t | bad = bad
infer Γ (App e e₁) | bad = bad
\end{code}

If all of this works, we know we have a term of type |WT Γ σ|, a term which is well-typed (with type |σ|) under the context |Γ|.
Note that a well-scoped term then has type |WT [] σ|, meaning it contains no references to variables which are not bound
in the term.  We can now get a |WT| term from concrete syntax with the following relatively painless invocation:


\ignore{

\begin{code}




open import Relation.Nullary.Core

-- we won't care about sorts here.
type2ty'  : Type → Maybe U'
type2ty' (el s (var x args)) = nothing
type2ty' (el s (con c args)) with type? c
type2ty' (el s (con c args)) | just x = just (O x)
type2ty' (el s (con c args)) | nothing = nothing
type2ty' (el s (def f args)) with type? f
type2ty' (el s (def f args)) | just x = just (O x)
type2ty' (el s (def f args)) | nothing = nothing
type2ty' (el s (lam v ty t)) = nothing -- type2ty ty => O {!!} -- err, we don't support types with lambdas (pi types)
--type2ty' (el s (pi (arg v r x) t₂)) = {!!} -- (type2ty x => type2ty t₂
type2ty' (el s (pi (arg v r x) t₂)) with type2ty' x | type2ty' t₂
type2ty' (el s (pi (arg v r x) t₂)) | just x₁ | just x₂ = just (x₁ => x₂)
type2ty' (el s (pi (arg v r x) t₂)) | just x₁ | nothing = nothing
type2ty' (el s (pi (arg v r x) t₂)) | nothing | b = nothing
type2ty' (el s (sort x)) = nothing
type2ty' (el s unknown) = nothing
-- if you get an incomplete
-- pattern matching here... this happens when a lambda wasn't
-- annotated. the Type is then `unknown', even though that's not a
-- constructor of type Type

type2ty'just : Type → Set
type2ty'just t with type2ty' t
... | nothing = ⊥
... | just x  = ⊤

type2ty : (t : Type) → type2ty'just t → U'
type2ty t pf with type2ty' t
type2ty t pf | just x = x
type2ty t () | nothing

mutual
  isVarReasonable : ℕ → List (Arg Term) → Set
  isVarReasonable x  l         with length l ≟-Nat 0
  isVarReasonable x  []                | yes p = ⊤
  isVarReasonable x₁ (x ∷ l)           | yes ()
  isVarReasonable x  l                 | no ¬p with length l ≟-Nat 1
  isVarReasonable x  []                | no ¬p  | yes ()
  isVarReasonable x₁ (arg a b c ∷ [])  | no ¬p  | yes p = isLambdaQ' c
  isVarReasonable x₂ (x ∷ x₁ ∷ l)      | no ¬p  | yes ()
  isVarReasonable x ls | no ¬p₁ | no ¬p with length ls ≤? 2
  isVarReasonable x [] | no ¬p₁ | no ¬p | yes p = ⊥
  isVarReasonable x₁ (arg v r x ∷ []) | no ¬p₁ | no ¬p | yes p = ⊥
  isVarReasonable x₂ (x ∷ x₁ ∷ []) | no ¬p₁ | no ¬p | yes p = ⊥
  isVarReasonable x₃ (x ∷ x₁ ∷ x₂ ∷ ls) | no ¬p₁ | no ¬p | yes (s≤s (s≤s ()))
  isVarReasonable x [] | no ¬p₂ | no ¬p₁ | no ¬p = ⊥
  isVarReasonable x₁ (arg v r x ∷ ls) | no ¬p₂ | no ¬p₁ | no ¬p = ⊥
  
  isLambdaQ' : (t : Term) → Set
  isLambdaQ' (lam v sigma t) = type2ty'just sigma × isLambdaQ' t
  isLambdaQ' (var a b)       = isVarReasonable a b
  isLambdaQ' (def f args)    = ⊥
  isLambdaQ' (con c args)    with type? c
  isLambdaQ' (con c args) | just x = ⊤
  isLambdaQ' (con c args) | nothing = ⊥
  isLambdaQ' (pi t₁ t₂)      = ⊥
  isLambdaQ' (sort x)        = ⊥
  isLambdaQ' unknown         = ⊥



term2raw :  (t : Term) →
            {pf : isLambdaQ' t} →
            Raw
term2raw (lam v sigma t)           {(pf₀ , pf)} = Lam (type2ty sigma pf₀) (term2raw t {pf})
term2raw (var x  l)                {pf}  with length l ≟-Nat 0
term2raw (var x  [])               {pf}        | yes p = Var x
term2raw (var x₁ (x ∷ l))          {pf}        | yes ()
term2raw (var x  l)                {pf}        | no ¬p with length l ≟-Nat 1
term2raw (var x  [])               {pf}        | no ¬p  | yes ()
term2raw (var x₁ (arg a b c ∷ [])) {pf} | no ¬p  | yes p = App (Var x₁) (term2raw c {pf})
term2raw (var x₂ (x ∷ x₁ ∷ l))     {pf} | no ¬p  | yes ()
term2raw (var x ls)                {pf} | no ¬p₁ | no ¬p with length ls ≤? 2
term2raw (var x [])                {()} | no ¬p₁ | no ¬p | yes p
term2raw (var x₁ (arg v r x ∷ [])) {pf} | no ¬p₁ | no ¬p | yes p = ⊥-elim (¬p refl)
term2raw (var x₂ (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) {()} | no ¬p₁ | no ¬p | yes p
term2raw (var x₃ (x ∷ x₁ ∷ x₂ ∷ ls)) {pf} | no ¬p₁ | no ¬p | yes (s≤s (s≤s ()))
term2raw (var x [])                 {()} | no ¬p₂ | no ¬p₁ | no ¬p
term2raw (var x₁ (arg v r x ∷ []))  {pf} | no ¬p₂ | no ¬p₁ | no ¬p = ⊥-elim (¬p₁ refl)
term2raw (var x₂ (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) {()} | no ¬p₂ | no ¬p₁ | no ¬p
term2raw (var x₃ (arg v r x ∷ arg v₁ r₁ x₁ ∷ x₂ ∷ ls)) {()} | no ¬p₂ | no ¬p₁ | no ¬p
term2raw (def f args)      {()}
term2raw (con c args)      {pf} with type? c
term2raw (con c args)      {pf} | just x = Lit x (quoteVal x (con c args))
term2raw (con c args)      {()} | nothing
term2raw (pi t₁ t₂)        {()}
term2raw (sort x)          {()}
term2raw unknown           {()}


typechecks : Raw → Set
typechecks r with infer [] r
typechecks .(erase t) | ok τ t   = ⊤
typechecks r          | bad      = ⊥


-- given a Raw lambda plus a proof (⊤) that it typechecks;
-- give the type of the expression.
typeOf : (r : Raw) → {pf : typechecks r} → U'
typeOf r {pf} with infer [] r
typeOf .(erase t) | ok τ t = τ
typeOf r {()}     | bad

raw2wt : (r : Raw) → {pf : typechecks r} → WT [] (typeOf r {pf})
raw2wt r {pf} with infer [] r
raw2wt .(erase t) | ok τ t = t
raw2wt r {()}     | bad


\end{code}
}


\begin{code}
exampleTerm : WT []      (   typeOf (   term2raw (quoteTerm (\ (x : ℕ) → x))))
exampleTerm =                raw2wt (   term2raw (quoteTerm (\ (x : ℕ) → x)))

explained      : typeOf (term2raw (quoteTerm (\ (x : ℕ) → x)))
               ≡ O Nat => O Nat
explained = refl

explained₁ : exampleTerm ≡ Lam (O Nat) (Var here)
explained₁ = refl
\end{code}

\subsection{Doing Something Useful with |WT|}

Conversely, we can also construct a term in |WT| and use the |unquote| keyword to
turn it back into concrete syntax.... . . . ..  %TODO explain this, also make a note about lack of APPLY construct, and the hack I do.



\section{Example: CPS Transformation}

Given the fact that we can now easily move from the world of concrete Agda syntax to a well-typed lambda calculus and back,
the obvious next step is to do something with these well-typed terms. Doing anything with these terms constitutes
a program transformation, since lambda terms represent simple programs. An additional bonus feature we now have at our
disposal is the ability to do these transformations while ensuring that certain properties (notably the well-typedness of
our terms) are not violated (preserved?).

The first case study in this area is that  of transforming lambda terms into continuation-passing style (CPS).
The idea of CPS is not new; it is what happens when you take the primitive idea of computer programming, which
essentially involves calling functions and returning values after their completion, and remove the notion
of returning \cite{asai2011introduction}.\todo{elaborate}
This seems both profound and unusable, yet it turns out to be a useful
paradigm for many applications \cite{krishnamurthi2007programming}.
Consider the example where you want to print an integer, but before doing so, would like
to call, on that number, the function which increases integers by 1. That might look something like
this:

\begin{spec}
main = print (suc 5)
\end{spec}

If the idea of \emph{returning} values is forbidden, how then must one \emph{continue}? The answer is
to do a transformation on the code; a continuation-passing style transformation. This name refers
to the fact that functions which would normally do something analogue to issueing a \texttt{return} statement,
are passed, as an additional parameter, a function to call on the result, instead of \texttt{return}.

The following translation provides an example.

\begin{code}
factorial : ℕ → ℕ
factorial 0         = 1
factorial (suc n)   = (suc n) * (factorial n)

factCPS : {a : Set} → ℕ → (ℕ → a) → a
factCPS   0        k      = k 1
factCPS (suc n)    k      = factCPS n (\ f -> mult f (suc n) k)
  where
    mult : {a : Set} → ℕ -> ℕ -> (ℕ → a) → a
    mult n m k = k (n * m)
\end{code}

Here we have translated the function by adding a new parameter (called |k|) which is called on the original
result of the computation, instead of just returning that result. In the base case the translation was trivial,
but in the inductive case we have to do a little more work. There, we immediately call the function recursively,
asking for the factorial of the next smaller number, but providing a continuation which combines the result of
that computation with the ``current'' value of $n$. We multiply the result of the recursive call with the current
value of $n$ by calling the |mult| function, which is also in continuation passing style; the result of this multiplication
is what we would like to return, which is why we provide $k$ as the continuation function.

We can now use this function in the traditional way if we pass the identity function as our continuation. This way,
the result of the computation is returned unchanged. Notice, though, that the type of the CPS-transformed function
is necessarily different from the original function.

\ignore{
\begin{code}
id : {A : Set}  → A → A
id x = x
open  import Relation.Binary.EqReasoning

RT : U'
RT = O ReturnType

\end{code}
}

Some anecdotal evidence that our CPS-transformed function does, indeed, perform
as we expect it to.


\begin{code}
equivFact1 : factorial 1 ≡ factCPS 1 id
equivFact1 = refl
equivFact5 : factorial 5 ≡ factCPS 5 id
equivFact5 = refl
\end{code}

%TODO wouter's "background reading on CPS"

This transformation can be done in a mechanical way, too. Also the type we
expect the new function to have can be derived. This is discussed at length by
Might \cite{might-cps}, whose implementation was also used as inspiration for this type-safe version.

The type of a CPS-transformed function can be computed as follows, where |RT| stands
for some return type.

\begin{code}
cpsType : U' → U'
cpsType (O x)     = O x
cpsType (t => t₁) = cpsType t => ((cpsType t₁ => RT) => RT)
cpsType (Cont t)  = cpsType t => RT
\end{code}

The type we would like our transformation function to have is something which takes
as input a term with some environment and type (|WT Γ σ|), a
continuation (necessarily |WT (map cpsType Γ) (cpsType σ => RT)|) and returns a
semantically equal term with type |WT (map cpsType Γ) RT|. In other words, the continuation
function must not rely on any variables which are not in the scope of the to-be-transformed function,
and must produce a value of type |RT|.%TODO maybe make this arbitrary...
If these are then applied to each other, a value of type |RT| should be returned.

The term of type |TAcc wt| which is also included will be explained later, and has to do
with termination of the function.

\ignore{
\begin{code}

noApp : {σ : U'} {Γ : Ctx} → WT Γ σ → Set
noApp (Var inpf)   = ⊤
noApp (Lam σ wt)   = ⊤
noApp (wt ⟨ wt₁ ⟩) = ⊥
noApp (Lit x )     = ⊥


cpsvar : forall {t g} → t ∈' g → (cpsType t) ∈' (map cpsType g)
cpsvar   here    = here
cpsvar (there v) = there (cpsvar v)

-- show that we can add more variables to our environment for free;
-- variables that used to be in the environment are still there 
weakvar : forall {τ Γ} → (τ' : U') → (Γ' : Ctx) → τ ∈' (Γ' ++ Γ) → τ ∈' (Γ' ++ (τ' ∷ Γ))
weakvar t' [] x = there x
weakvar t' (x ∷ env) here = here
weakvar t' (x ∷ env) (there x₁) = there (weakvar t' env x₁)


-- show that we can add a type variable somewhere in the middle of our
-- environment and stuff still is okay.
weak : forall {Γ' τ Γ} → WT (Γ' ++ Γ) τ → (τ' : U') → WT (Γ' ++ (τ' ∷ Γ)) τ
weak (Lit x) t = Lit x
weak {Γ'} (Var x) t' = Var (weakvar t' Γ' x)
weak {g'} {t => t1} (Lam .t e) t' = Lam t (weak { t ∷ g' } e t')
weak {g'} {t2} {g} (_⟨_⟩ .{_}{t1}.{t2} e1 e2) t' =
               (weak {g'} {t1 => t2} e1 t')
               ⟨   (weak {g'} {t1} e2 t') ⟩
 
-- increase all the de Bruijn indices by 1. Needs to have some
-- arbitrary type added to the front of the environment to keep
-- the lengths right. special case of weakening, but with empty prefix environment.
shift1 : forall {Γ τ} → (τ' : U') → WT Γ τ → WT (τ' ∷ Γ) τ
shift1 t' e = weak {[]} e t'


data TAcc : {Γ : Ctx} {σ : U'} → WT Γ σ → Set where
  TBaseLit : forall {Γ σ x} → TAcc (Lit {Γ} {σ} x)
  TBaseVar : forall {Γ σ x} → TAcc (Var {Γ} {σ} x)
  TLam : forall {Γ t1 t2} {a : WT (t1 ∷ Γ) t2}
         --→ TAcc a
         → TAcc (shift1 (Cont t2) a)
         → TAcc {Γ} {t1 => t2} (Lam {Γ} t1 a)
  TApp : forall {Γ σ σ₁} {a : WT Γ (σ => σ₁)} {b : WT Γ σ}
         → TAcc {Γ} {σ => σ₁} a
      --   → TAcc b
         → TAcc (shift1 (σ => σ₁) b)
         → TAcc (a ⟨ b ⟩)


\end{code}
}
\begin{code}
T : {σ : U'} {Γ : Ctx}       → (wt : WT Γ σ)
                             → TAcc wt
                             → WT (map cpsType Γ) (cpsType σ => RT)
                             → WT (map cpsType Γ) RT
\end{code}

The case for literals and variables is, as usual, not very difficult. All that happens here is
that the continuation function is applied to the original term, and in
the case of variables, some housekeeping (a proof is given that if some variable with type |σ| is inside the
environment |Γ|, then it will also be inside the new environment |map cpsType Γ|, but having type |cpsType σ|)  is done.

\begin{code}
T (Lit x)             TBaseLit                    cont = cont ⟨ (Lit x) ⟩
T (Var inpf  )        TBaseVar                    cont = cont ⟨ (Var (cpsvar inpf)) ⟩
\end{code}

The case for lambdas is slightly more involved; the body is recursively CPS transformed, and a new abstraction is
introduced ...

\begin{code}
T {t1 => t2} (Lam .t1 expr)     (TLam pf)     cont = cont ⟨ (Lam (cpsType t1)
                                                                 (Lam (cpsType t2 => RT)
                                                                      (T (shift1 (Cont t2) expr) pf
                                                                         (Var here)
                                                                      )
                                                                 )
                                                            )
                                                          ⟩

\end{code}

Finally, we have the application case.

\begin{code}
T .{σ₂} (_⟨_⟩ .{_}{σ₁}{σ₂} f e) (TApp pf pf2) cont =
   T f pf (Lam (cpsType σ₁ => ((cpsType σ₂ => RT) => RT))
                           (T (shift1 (σ₁ => σ₂) e) pf2 (Lam (cpsType σ₁)
                              (((Var (there here)) ⟨ (Var here) ⟩ ) 
                                  ⟨ (shift1 (cpsType σ₁) (shift1 (cpsType σ₁ => ((cpsType σ₂ => RT) => RT)) cont)) ⟩ ))))


\end{code}
\begin{code}

\end{code}








Maybe we can give a Bove-Capretta example here, too, since |T| uses general recursion.

% TODO how to strike a balance between just presenting what I have now without making
% the difficulties clear, and writing an irrelevant logbook?

Could be an idea to prove correctness by normalisation and translation back into lambda calculus.

\section{Example: Translation to SKI Combinators}

hullo

\chapter{Generic Programming}\label{sec:generic-programming}

Ornaments / containers?
will we ever get here?

\chapter{Miscellaneous}
\section{Implicit Record-type Arguments}\label{sec:implicit-unit}

As has been noted before, if a particular argument is a record type,
and it has only one possible inhabitant, Agda can
automatically infer its value. Thus, it also need not be passed as an explicit argument
at the call-site. The following code snippet (Fig. \ref{code:implicit-example}) illustrates
how record type arguments having only one alternative can be automatically inferred.

The function |foo| expects a value of type |⊤ × ⊤|, and returns a natural number.
We know, however, that | _×_ | is a record and only has the constructor | _,_ : A → B → A × B| (this pair type
is a special case of the dependent pair |Σ (A : Set) (B : A → Set) : Set|), therefore the only
possible value is one using the constructor |_,_|. If we next look at the values for |A| and |B| here,
namely the left and right-hand arguments' types, we see that in both cases they have type |⊤|. The
unit type also is defined as a record with only one constructor, namely |tt|. This means that the 
only value possible is |tt , tt|, which is why we can use the underscore-notation, meaning
Agda should infer the argument for us.

The fact that pairs and unit are defined as records in the standard library is pretty crucial here.
The type system does some work for us in these cases: since eta-conversion is done on record types, which
allows Agda to infer that there is exactly one inhabitant of a certain type. This eta reduction is not done
on general data types, since this would increase the complexity of the work the compiler needs to do as
well as potentially introduce unsound behaviour \cite{mcbride-motivation-eta-rules}.


\begin{figure}[h]
\begin{code}
foo : ⊤ × ⊤ → ℕ
foo u = 5

bar : ℕ
bar = foo _
\end{code}
        \caption{Illustrating the automatic inference of record arguments.}
        \label{code:implicit-example}
    \end{figure}
Since this inference is possible, we can also make this argument implicit, which effectively
hides from the user that a value is being inferred and passed, as in Fig. \ref{fig:implicit0}.
    
    \begin{figure}[h]
\begin{code}
foo' : {u : ⊤ × ⊤} → ℕ
foo' = 5

bar' : ℕ
bar' = foo'
\end{code}
        \caption{Implicit (or hidden) arguments are inferred, if possible.}
        \label{fig:implicit0}
    \end{figure}

%todo use the term "proof irrelevance"
    
This is possible, since the type |⊤ × ⊤| only has one inhabitant, namely |(tt , tt)|. If
multiple values were valid, the above code would have resulted in an unsolved meta. That brings
us to one of the drawbacks of this solution which has been used quite often (chiefly to ``hide''
a proof witness of for example an input term being of the right shape), which is that if such
an argument is ambiguous, or worse, if it is a type with no inhabitants, the compiler won't fail
with a type error, but merely with an unsolved meta warning (highlighting the piece of code yellow
in the Emacs Agda mode). This is particularly unfortunate when we are using this technique
to hide an inferrable proof of the soundness of a theorem, such as in the boolean tautology example (Sec.~\ref{sec:boolexpr}).
The thing is, we do not want a user to get away with being able to prove that something which is not a
tautology, is a tautology. Since the proof that under all environments the theorem evaluates
to true is an implicit argument in this style, one is merely left with an unsolved meta, which
might seem a triviality if one doesn't read the compiler's output carefully. Luckily Agda disallows
importing modules with unsolved metas, which means such a spurious proof will not be usable elsewhere
in a real-life development. 


\section{Reflection API Limitations}\label{sec:reflection-api-limitations}


\begin{itemize}
\item Cannot call |unquote| on non-constructor term. I.e. |unquote (lam2term t)|
\item Impossible to introduce definitions
\item Inspection of functions (e.g. clauses) not implemented
\item ?? creation of pattern-matching functions not possible => bove capretta impossible (or maybe completely automatic GP impossible)
\item untyped terms are returned. this is solved.
\end{itemize}


\chapter{Discussion}
\label{sec:discussion}

This paper has presented two simple applications of proof by
reflection. In the final version, we will show how
Agda's reflection API has several other applications.

%\chapter{Conclusion}\label{sec:conclusion}
% is this even a real separate section? Isn't discussion enough?

Answer the research question here.

\appendix

% \appendixpage

\chapter{Modifications to the Agda Compiler}

During the course of this project, a few modifications were made to the Agda
code base, to facilitate various processes. Since these modifications have
not yet been included in the main code repository, anyone interested in trying out the
changes is invited to make a clone of the forked repository where the development was
done.

The compiler can be found at \url{https://darcs.denknerd.org/Agda}, and the modified standard library
(modified to work with the updated data types in the compiler) can be found at \url{https://darcs.denknerd.org/agda-stdlib}.
The instructions for installation of Agda from source, on the Agda wiki\cite{agda-wiki-installation}, can be followed
unmodified.

The modifications made are the following.

\begin{itemize}

\item The output of the reflection system (in other words the |Term| data type)
was modified to include type annotations on lambda abstractions. See Sec.~\ref{sec:annotating-lambdas}.
\item For convenience of producing syntax-highlighted documents from Literate Agda,
the compiler was extended to output a list of formatting rules based on the currently in-scope identifiers. See Sec.~\ref{sec:lhs-syntax}.
\end{itemize}



\section{Annotating |λ| Expressions with Type}\label{sec:annotating-lambdas}

As mentioned in Sec.~\ref{sec:...} it was necessary to slightly modify the
representation of |Term|s that the reflection system returns to the user. What was
needed was to annotate lambda abstractions with the type of their argument, since without
this, type inferencing would be necessary. However possible, this would introduce unneeded complexity
and open the can of worms that is type unification. As it turns out, the termination of
type unification algorithms is something rather nontrivial to prove, as pointed out by McBride \cite{mcbride2003first}.
To avoid this, the |Term| data structure internal to the Agda compiler was augmented with an
optional field of type |Type|, which allowed two advantages. Firstly, it became possible to
distinguish between, for example, |ℕ| and |Bool| variables in the same expression. Secondly, it
allowed us to suffice with only providing a type checker, as opposed to a full type inferencing
function along with the unification, which poses a problem to the termination checker.

Here the changes required to the Agda compiler's source code are presented in Fig. \ref{fig:agda-lambda-diff}, in unified diff format \cite{unified-diff}.


\begin{figure}[h]
insert darcs-diff here %TODO
\caption{The changes required to the Agda compiler to enable annotation of lambda abstractions with the type of their argument.}\label{fig:agda-lambda-diff}
\end{figure}





\section{Automatic Syntax Highlighting for Literate Agda}\label{sec:lhs-syntax}

Talk about extension to compiler here, give example of use (as detailed as possible, i.e. with Makefile, the --lagda flag, etc.





% TODO: explain somewhere how the distribution works. i.e. `mk extract` for code extraction, what module contains what, etc.




%TODO in introduction: list motivating examples for using reflection? include bove-capretta, so we later can conclude reflection API isn't yet powerful enough?

%TODO compare the tauto-solver to tactics, note how this is embedded in agda and not some sub-language of coq (for in the discussion, perhaps)

%todo what are Patrick Bahr's tree automata?

%TODO: Dependently typed LC is difficult to type check: Outrageous but Meaningful Coincidences -- McBride.




\bibliography{refs}{}
\bibliographystyle{plain}
% \bibliographystyle{splncs}%this one doesn't sort automatically. :(


% Gebruik geen contractions isn't, didn't etc.
% Beperk je tot de essentie
% Geef voorbeelden

\end{document}
%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "lagda2pdf"
%%% End: 
