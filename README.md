Reflection in Agda
==================
MSc project in Computing Science  
[Department of Computing Science, Utrecht University](http://www.cs.uu.nl)  
Project supervisor: [Wouter Swierstra](http://www.staff.science.uu.nl/~swier004/)

This is a project exploring the uses and limitations of the reflection API recently included in [Agda](http://wiki.portal.chalmers.se/agda/), the dependently typed programming language slash interactive theorem prover.

This repository contains two main components, Proofs and Metaprogramming. Proofs contains an example of how to use the reflection API to accomplish a technique ambiguously named proof by reflection (referring to another type of reflection than the programming language technology reflection as is present in, for example, Lisp).

The Metaprogramming collection of sources illustrates how various tasks (such as program transformation) can be carried out in a type-preserving way, without losing any shiny automation that reflection allows us to implement. Two example  program transformations of simply typed lambda calculus with De Bruijn indices are implemented: a translation to SKI combinators, and a CPS (continuation-passing style) transformation.

Also included in this repository is the final thesis for the project, which goes into a lot of detail on the techniques used, and might be useful should anyone want to use the reflection API for their own purposes, since many common pitfalls are highlighted and solved. The library `Autoquote` is also included, which automates quoting of Agda terms to basic inductive data types for your own AST.

Questions and comments are of course welcome; my email address is my first name at my domain dot org, which can be found in my GitHub profile.

Paul van der Walt  
https://denknerd.org

Using the package
-----------------

The code included in this repository can be used as a convenient starting point for doing your own reflective development; all of it should compile fine in bleeding edge darcs Agda (currently version 2.3.1). You could conceivably also want to prove the evenness of certain naturals, or maybe do a CPS transformation on some of your lambda expressions. Examples of how to achieve this are given in the modules prefixed with `Example`, so have a peek how that works there.

Note on compiler modifications
------------------------------

At the time of writing, the code presented here does not work as advertised: a slightly modified version of the Agda compiler is required. Why this is needed, and what modifications are involved, is explained in detail in the [thesis](https://github.com/toothbrush/reflection-proofs/downloads) this code supports – please have a look at Appendix A.1 there before telling me my code doesn't compile.
