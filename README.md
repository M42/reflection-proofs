Reflection in Agda
==================

This is a project exploring the uses and limitations of the reflection API recently included in Agda, the dependently typed programming language slash interactive theorem prover.

This repository contains two main components, Proofs and Metaprogramming. Proofs contains an example of how to use the reflection API to accomplish a technique ambiguously named proof by reflection (referring to another type of reflection than the programming language technology reflection as is present in, for example, LISP, and recently Agda).

The Metaprogramming collection of sources illustrates how various tasks (such as program transformation) can be carried out in a type-safe way, without losing any shiny automation that reflection allows us to implement. Two examples of program transformation which have been implemented are simply typed lambda calculus with de Bruijn indices to SKI combinators, and a CPS (continuation-passing style) transformation on the same lambda terms.

Also included in this repository is the final thesis for the project, which goes into a lot of detail on the techniques used, and should be useful should anyone want to use the reflection API for their own purposes, since many common pitfalls are highlighted and solved.

Questions and comments are of course welcome; my email address is first name at my domain dot org, which can be found in my GitHub profile.

Paul van der Walt
