Shared increment-body search
============================

Run:
  python3 -B research/search_addition.py 3

This enumerates short ordered binary addition DAGs for the constructor's
repeated increment body, allowing at most three extra shared reader nodes.
The starting source is the pinned QN reader grammar. Existing inc1 and
inc2 controls are kept; the old coefficient-four root can have new children.
Each candidate counts the complete raw controls and computes a maximum
matching of the inherited one-predecessor-bit, three-step selector folds.

The fresh run examined 1,486 candidate DAG descriptions. Its best optimistic
net score was 194. The only descriptions at that score have coefficients
four, five, or six. No candidate below 194 was found in this search.

A natural coefficient-eight body is 8=4+4,4=2+2. It has 202 raw controls,
but the inc2 reader receives both history bits, invalidating the extra
41-to-99 fold used in the coefficient-five/six constructions. Seven retained
folds therefore give 195, not 194, for that direct construction.

These are restricted, finite search results. The score is an optimistic
disjoint-pair matching: not every arbitrary combination of offered folds
has separately passed the final simultaneous local checker. No claim is
made that all candidate DAG descriptions are different machines. Neither
this search nor its negative result proves a lower bound on general
Turing machines, alternate logical calculi, or larger source rewrites.
