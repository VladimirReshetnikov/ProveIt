EXACT FINITE CHECKS FOR BLIND-OUTPUT GAMES
========================================

Run with Python 3.9 or newer:

    python3 verify_finite.py > finite_results.json

The script uses only Python's standard library. It uses integers and
fractions.Fraction throughout; no random sampling or floating-point
optimization is used. Output is deterministic JSON. An incorrect check
raises AssertionError and exits unsuccessfully.

1. Exhaustive finite blind maps
------------------------------

On the binary n-cube, a blind output chooses a coordinate and a guessed
value. Blindness requires that changing that chosen coordinate leave the
output unchanged. Thus each vertex is paired with its neighbor on the
chosen coordinate. These pairs form a perfect matching, and each edge
has one of two guess labels. Conversely, any such edge-labeled matching
defines a blind output map. This is why enumerating these matchings
enumerates every blind output, rather than only a chosen family.

For n = 1, 2, 3, the program checks every resulting map and verifies that
exactly half the configurations succeed. The expected counts are:

    n        cube matchings        blind maps
    1               1                  2
    2               2                  8
    3               9                144

For n = 2, it checks all 8^3 = 512 ordered triples of maps, allowing
repetition. For each triple it computes the minimum, over the four
configurations, of the number of correct players. The maximum of these
guaranteed scores is 1 = floor(3/2). The JSON includes the distribution
of guaranteed scores and a complete attaining witness. Coordinate zero
is the leftmost coordinate in the displayed binary configuration.

2. Collision feasibility
------------------------

The script explicitly enumerates all values of each distinct external
target and computes the resulting success-bit patterns, holding specified
internal values fixed. Its examples include a shared binary target with
guesses (0,0,1), yielding precisely {001,110}; three distinct external
targets, yielding all eight patterns; an unused third alphabet value;
one fixed internal success; and two independent target-collision groups.

These are checks of finite algebraic feasibility. An external variable in
this calculation is an abstract free coordinate. It is not a construction
of a diffuse target law on a finite probability space.

3. Joint-law polytope equality
-----------------------------

Write Delta(T) for the probability simplex on the finite pattern set T.
Two two-player examples are checked exactly. Pattern coordinates have
order 00, 01, 10, 11.

Example A:

    (1/2) Delta({00,11})
  + (1/3) Delta({01,10})
  + (1/6) Delta({00,01,10,11}).

Example B:

    (1/4) Delta({00})
  + (1/4) Delta({01,11})
  + (1/2) Delta({10,11}).

For each example the program enumerates every weighted sum obtained by
choosing one vertex from each simplex. Their convex hull is the weighted
Minkowski sum. Independently, it constructs every subset Hall inequality

    p(U) <= sum of w_T over all T meeting U,

together with nonnegativity and total mass one. Exact Gaussian elimination
enumerates all vertices of the resulting bounded polytope, including
vertices of the lower-dimensional Example B. It verifies both that every
weighted selection sum satisfies the inequalities and that every Hall
vertex is one of the selection sums. These two containments establish
equality of the two polytopes for the given examples.

As a separate check, an integer maximum-flow implementation, after exact
common-denominator rescaling, tests membership at every probability-vector
lattice point of denominator 12 (Example A) or 8 (Example B). It compares
these results with direct Hall-inequality membership. There are 455 and
165 such points, respectively. No optimization library is needed.

4. Single-player interval specializations
----------------------------------------

For q in {2,3,5} and alpha in {0,1/4,1/2,3/4,1}, the same exact polytope
calculation uses forced-failure weight alpha(q-1)/q, forced-success weight
alpha/q, and free-pattern weight 1-alpha. It checks that the success
coordinate ranges exactly over

    [alpha/q, 1 - (q-1)alpha/q].

When alpha = 1, the endpoints coincide. These are finite rational checks
of the formula's algebra, not a proof that the weights arise from a
particular infinite game. On a finite target space every target law is
atomic, so alpha < 1 in this section is a formal feasibility-cell weight.

Scope
-----

These computations check small exhaustive instances and exact polytope
identities. The article's countable factorization, measurable envelopes,
Radon--Nikodym classification, and infinite-product claims require their
written proofs. This script does not verify those proofs or establish
historical novelty. No PDF is expected from this script.
