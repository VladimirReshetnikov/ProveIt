# Claim ledger

## Proved here

| Claim | Precise scope | Article |
|---|---|---|
| Exact equality keys | Reduced **noncyclic** C2*C3 state plus exponent is faithful for B3. | Lemma 2.1 |
| Linear corridor cover | Every two-index interval is covered; total corridor length ≤2n. | Lemma 3.2 |
| Optimal pass | Disjoint rank-two substitutions to identity or one support letter; deterministic O(n log n) word-RAM. | Theorem 4.1 |
| Repeated termination | At most n/2 shortening passes; conservative O(n² log n) word-RAM. Not a global shortest word. | Corollary 4.2 |
| Linear replay | ≤n/2 steps, ≤n/2 inserted nodes, ≤3n/2 removed nodes across all passes. | Theorem 5.1 |
| Constructive QP class | Flat rank-two inflations of O(log² n) cores; decomposition not supplied. | Theorem 6.3 |
| Arbitrary-strand positive family | 8m+s+23 letters reduce optimally to s−1, followed by elementary unknot certification. | Theorem 7.1 |
| Explicit survivor obstruction | Circleless matching-sum complexes for weaving prefixes; not all representations or scan orders. | Theorem 8.2 |
| Rank-two geodesic barrier | Explicit B4 unknots, immune to every strictly shortening rank-two replacement even with long targets. | Theorem 9.1 |
| Prefix-state transfer | Costed canonical-state primitives imply optimal finite-target interval DP. Higher-rank primitives are not implemented here. | Proposition 11.1 |

## Implemented and tested

The optimizer, AVL and hash dictionaries, persistent trie, independent replay,
input validation, transcript accounting, test family generation, slow oracles,
and small reduced-F2 Khovanov cube have the recorded completed tests.
The cube is exponential and resource-capped by default. Python code and human
proofs are supplied; they are not Lean-verified.

## Not established

There is no proof that arbitrary knot diagrams admit small residual cores.
There is no universal quasi-polynomial complexity bound for this recognizer.
There is no claim of globally shortest braids or complete Markov simplification.
There is no full upstream-pipeline benchmark, upstream regression run, executed
real-upstream adapter test, Rust port, or repository merge.
The measured speedups compare the primitive with its independent brute oracle.
The survivor theorem does not lower-bound all unknot-recognition algorithms.
No priority claim is made for standard braid-group or Khovanov background.
