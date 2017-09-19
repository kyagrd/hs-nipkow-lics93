# hs-nipkow-lics93
Haskell port of [Tobias Nipkow's LICS 1993 paper](https://www21.in.tum.de/~nipkow/pubs/lics93.html) on Higher-Order Pattern Unification using the [Unbound](https://hackage.haskell.org/package/unbound) libirary.

The main function runs the Example 3.2 in Nipkow's paper.

TODO: The code here is trying to do a bit more than the paper. The code of the paper only describs solving the unification problem of a single pair of higher-order patterns. However, what we almost always want is to solve a conjuction of unification pairs where some of the logic variables are shared among them. Now the code only works for a single pair. It seems to need some engineering to put it to process multiple pairs of unifications accumulating the substitutions from previous pairs.
