Engineering Proof by Reflection in Agda
==================
**Hint**: if you are looking for the MSc project "Reflection in Agda", see [here](https://github.com/toothbrush/reflection-proofs/tree/msc-thesis).  
[Department of Computing Science, Utrecht University](http://www.cs.uu.nl)

Paul van der Walt and [Wouter Swierstra](http://www.staff.science.uu.nl/~swier004/)

This is a project exploring the uses and limitations of the reflection API recently included in [Agda](http://wiki.portal.chalmers.se/agda/), the dependently typed programming language slash interactive theorem prover.

This repository contains the code to accompany the paper "Engineering Proof by Reflection": an example of how to use the reflection API to accomplish a technique ambiguously named proof by reflection (referring to another type of reflection than the programming language technology reflection as is present in, for example, Lisp).

Also included in this repository is the article, which goes into some detail on the techniques used, and might be useful should anyone want to use the reflection API for their own purposes. The library `Autoquote` is also included, which automates quoting of Agda terms to basic inductive data types for your own AST.

Questions and comments are of course welcome; my email address is my first name at my domain dot org.

Paul van der Walt  
http://www.denknerd.org

Using the package
-----------------

The code included in this repository can be used as a convenient starting point for doing your own reflective development; all of it should compile fine in mainline Agda (currently version 2.3.2). You could conceivably also want to prove the evenness of certain naturals, no one is going to hold you back there. Examples of how to achieve this are given in the modules prefixed with `Example`, so have a peek how that works there.

Reference to master thesis / self-plug
--------------------------------------

This paper covers a small portion of what the original master thesis covers, in a lot less detail. Inquisitive readers are encouraged to take a look at the  [thesis](https://github.com/downloads/toothbrush/reflection-proofs/ReflectionProofs.pdf); more extensive  [code](https://github.com/toothbrush/reflection-proofs/tree/msc-thesis)  can be found in the `msc-thesis` branch.
