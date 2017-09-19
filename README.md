# hs-nipkow-lics93
Haskell port of [Tobias Nipkow's LICS 1993 paper](https://www21.in.tum.de/~nipkow/pubs/lics93.html) on Higher-Order Pattern Unification using the [Unbound](https://hackage.haskell.org/package/unbound) libirary.

The main function runs the Example 3.2 in Nipkow's paper.

The code here is actually doing a bit more than the paper. We almost always want is a conjuction of several unification equations where some of the logic variables are shared among implementation.
