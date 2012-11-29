IFL2012 submission
==================

**Engineering Proof by Reflection in Agda**

Tips for using this distribution
--------------------------------

In this directory, `doc`, you will find the Literate Agda sources for the IFL
submission "Engineering Proof by Reflection in Agda". There is a Makefile which
should make the usual tasks easy, but for the inquisitive, a little more
information is provided here.

Prerequisites
-------------

To be able to do anything useful with these sources, you will need a few software
packages installed and working. A few, but not all, dependencies are listed here.

* Haskell Platform (or at the very least a working GHC; Cabal will make your life easier)
* Agda v2.2.8 or later (doing `cabal install agda` should be enough)
* LHS2TeX
* A sensible pdflatex installation
* Rubber (available from Your Favourite Package Manager™)

The Makefile targets
--------------------

The included Makefile has a few targets. Most likely you will want to compile the article
for yourself -- this is also the default target. This will run LHS2TeX on the Literate
Agda file, then use `rubber` to compile the paper.

If you'd like to extract the code and play around with it, without having the added
distraction of all the LaTeX code around it, you will probably want to use `make extract`. This
target will place a file called `ReflectionProofs.agda` in the `extracted` subdirectory. If you
would like to type check the generated file, without opening the Emacs Agda interface, just run
`make check` -- this allows you to do development the primitive way.
