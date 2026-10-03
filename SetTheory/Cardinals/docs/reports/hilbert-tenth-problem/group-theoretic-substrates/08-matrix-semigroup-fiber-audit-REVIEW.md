# Independent review

Date: 2026-10-03
Status: PASS

The complete proof and the main checker were reviewed independently of their
author. The review confirmed:

- Unique separator parsing and the one-rule-per-block invariant
- Collision-free stutter insertion, including repeated lengths and merging
  cleanup paths
- Exact binomial cleanup multiplicity and minimum core tile length
- The exact rational generating function and its properness identity
- Support at r_*, r_*+2, and every r>=r_*+4, with the two stated holes
- The exact all-nonnegative-r quasipolynomial, pole orders, leading
  asymptotic, cumulative count, and generalized inverse
- The actual accepting tape's weights, coefficient denominator, period
  bound, and nonoscillatory top four coefficients
- Separation between fixed-r finite fibers and the infinite disjoint union
  over r, and the special zero-step target X

`independent_check.py` was authored independently of `check_fibers.py` and
of the source matrix/paired compilers. It enumerates literal bottom-side
tile partitions, builds weighted reachable graphs, and propagates counts
forward from each input. This differs from the main checker's backward
recurrence and does not import that code. Its checked fixtures are the
actual accepting tape and all 225 already-halting configurations whose
left/right binary contexts have length at most three.

The copied independent checker's sole modification was replacing its
original external data pathname by the local relative `data/semigroup.json`
path. Its original SHA-256 input pin is retained. Normal and Python -O
replays agree byte-for-byte: 226 cases, 31,366 coefficient comparisons,
and maximum genuine cleanup multiplicity 20.

The independent proof review and bounded checks support the supplied
argument; they are not a machine-checked formal proof or a nonhalting test.
