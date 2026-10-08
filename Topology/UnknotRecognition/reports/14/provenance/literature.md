# Literature and repository audit: unknot complexity

Research date: 7 October 2026. This is an internal synthesis for the main
article, not a claim to have independently verified every cited proof.

## 1. The quasi-polynomial target has a specific exponent

Marc Lackenby's March 2021 Oxford slides announce an unknot-recognition
algorithm taking `2^{O((log n)^3)} = n^{O((log n)^2)}` time on an n-crossing
diagram. This is quasi-polynomial but is not the stronger `n^{O(log n)}`.
The slides give the intended envelope: surface complexity `O(n^2)`,
compressed normal-surface operations, multi-surfaces, and hierarchy length
`O((log n)^2)`. Generalised Heegaard splittings and Cheeger regions are
central to the last bound.

Primary sources:

- https://people.maths.ox.ac.uk/lackenby/quasipolynomial-talk-oxford.pdf
  (web refs `turn11view2`, `turn12view0`, `turn12view1`; PDF pages 72–73,
  83–89, 105–108 are particularly relevant).
- https://www.math.princeton.edu/events/unknot-recognition-quasi-polynomial-time-2021-04-15t193000
  (`turn0search1`), an official contemporary announcement.
- https://people.maths.ox.ac.uk/lackenby/ (`turn1view1`), inspected current
  author publication/preprint list, with CV dated September 2026.

The careful present-tense statement is: the bound is announced in primary
talk material; the sources located do not establish that its complete
algorithm/proof has appeared as a paper. Do not call our scanner an
implementation of that algorithm.

## 2. Major fresh source: July 2026 hierarchy paper

Marc Lackenby, *Incompressible surfaces, hierarchies and unknot recognition*,
arXiv:2607.23350v1, 25 July 2026, 54 pp. The arXiv record currently contains
only v1.

- Abstract/version: https://arxiv.org/abs/2607.23350 (`turn11view0`).
- Full text: https://arxiv.org/html/2607.23350v1 (`turn1view0`, `turn4view1`,
  `turn7view3`).

Section 9 explicitly distinguishes an iteration bound from an implemented
runtime bound. Proposition 9.1 gives `L(g+1)^L` iterations, where L bounds
hierarchy length and g bounds pattern-complexity. Section 10 removes
interior parallelity bundles and bounds length by `4 c_q(H_initial)`;
`c_q(H)=sum_H max(I(H),0)^2`. Section 14 supplies efficient hierarchy
encoding and polynomial verification, using uniform handle types and
logarithmically encoded normal weights. Proposition 14.2 and Theorem 14.4
give relevant polynomial-time compressed cutting operations under their
stated hypotheses. The word "quasi" does not occur in the full text.

Thus this is highly relevant constructive progress, but is not itself a
published quasi-polynomial runtime theorem. The distinction between small
certificates and efficiently finding them remains essential.

### Derived complexity interface (our elementary consequence)

Suppose an implementation has at most `L(g+1)^L` elementary phases and
each phase costs at most B bit operations. Then

`log_2 T <= log_2 B + log_2 L + L log_2(g+1) + O(1)`.

This makes the missing envelope explicit. A sufficient condition for
`2^{O(log^3 n)}` time is `log B + log L + L log(g+1)=O(log^3 n)`.
For example L=`O(log^2 n)`, g=`n^{O(1)}`, and polynomial B suffice.
The inequality is only a reduction of the runtime problem; it is not a
proof that the topological parameters obey those bounds.

## 3. Width does not bound Khovanov basis size

Tuomas Kelomäki and Dirk Schütz, *On computational complexity of Khovanov
homology*, arXiv:2601.02119v1 (5 January 2026), 30 pp.

- https://arxiv.org/abs/2601.02119 (`turn11view1`).
- https://arxiv.org/html/2601.02119v1 (`turn5view0`).

Theorem 1.2 proves exponential running time of the Bar-Natan scanning and
divide-and-conquer algorithms even on positive or alternating 3-braids.
Total Betti rank can grow exponentially, so an explicit basis cannot stay
small. Theorem 1.3 separately computes integer Khovanov homology of closed
3-braids in polynomial time through special structural formulas. Theorem
1.4 computes fixed-width extremal homological bands of fixed-strand braids
in polynomial time. General fixed-strand polynomial computation remains a
conjecture in this paper.

Consequence for our designs: Catalan-many boundary matchings count object
types only. One must additionally control multiplicities, differential
data, and arithmetic bit lengths. A tensor contraction proof for a scalar
invariant cannot be transferred unchanged to a chain-complex algorithm.
This source supplies a rigorous counterexample to that tempting argument.

The previously delivered 3-braid backend already exploits Theorem 1.3;
do not package it as this turn's new contribution.

## 4. Exact quantum invariants really do admit width bounds

Clément Maria, *Parameterized Complexity of Quantum Knot Invariants*,
SoCG 2021, LIPIcs 189, 53:1–53:17.

- https://doi.org/10.4230/LIPIcs.SoCG.2021.53
- https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SoCG.2021.53
  (`turn7view1`, `turn8view1`).
- Full PDF (`turn9view1`):
  https://drops.dagstuhl.de/storage/00lipics/lipics-vol189-socg2021/LIPIcs.SoCG.2021.53/LIPIcs.SoCG.2021.53.pdf

For module dimension at most N and diagram carving-width cw, the paper
gives `O(N^{(3/2)cw} poly(n))` time for the specified
Reshetikhin–Turaev invariants, including coloured Jones polynomials.

Own consequence: fixed N and cw=`O(log^2 n)` yield quasi-polynomial
invariant computation. If the invariant differs from its unknot value,
this is a sound nontriviality certificate. Equality alone is not a complete
unknot test. For growing N one must retain `cw log N` and exact coefficient
costs, rather than treating the local dimension as a constant.

## 5. A complete small-width class

Hans L. Bodlaender, Benjamin A. Burton, Fedor V. Fomin, and Alexander
Grigoriev, *Knot Diagrams of Treewidth Two*, WG 2020, LNCS 12301, pp. 80–91;
arXiv:1904.03117.

- https://arxiv.org/abs/1904.03117 (`turn6search0`).
- https://arxiv.org/pdf/1904.03117 (`turn6search15`).
- https://doi.org/10.1007/978-3-030-60440-0_7 (`turn6search20`).

They give linear-time unknot recognition, and unlink recognition, when the
underlying diagram graph has treewidth two. Their reductions also give at
most n twist/untwist and poke/unpoke moves for trivial diagrams in this
class. A dedicated implementation could expand a genuinely complete
tractable class; a general width-k claim would require additional theory.

## 6. A universal low-width diagram reduction is impossible

Corentin Lunel and Arnaud de Mesmay, *A Structural Approach to Tree
Decompositions of Knots and Spatial Graphs*, arXiv:2303.07982v2.

- https://arxiv.org/html/2303.07982v2 (`turn7view2`, `turn8view2`).

Their Corollary 1.3 proves that every diagram of torus knot T(p,q) has
treewidth at least `min(p,q)/3`. Their principal result relates spherewidth
to bubble tangles, and compression representativity supplies lower bounds.

Own implication: for consecutive large p,q, the standard crossing number
is quadratic in their size, while the unavoidable width is linear.
Therefore a proposed scheme that replaces every n-crossing knot diagram
by an equivalent polylogarithmic-treewidth diagram is false, irrespective
of how much diagram simplification one allows. This does not rule out
recognition algorithms that dispose of wide nontrivial knots through
other certificates, or special low-width certificates for unknots.

## 7. Fresh alternative practical filter: Hecke/HOMFLY-PT

Clément Maria and Hoel Queffelec, *A Fast Algorithm for the Hecke
Representation of the Braid Group, and Applications to the Computation of
the HOMFLY-PT Polynomial and the Search for Interesting Braids*, SoCG 2026,
LIPIcs 367, 76:1–76:18; full version arXiv:2512.06142.

- https://doi.org/10.4230/LIPIcs.SoCG.2026.76 (`turn7view0`, `turn8view0`).
- Full PDF (`turn9view0`):
  https://drops.dagstuhl.de/storage/00lipics/lipics-vol367-socg2026/LIPIcs.SoCG.2026.76/LIPIcs.SoCG.2026.76.pdf
- Supplementary implementation: https://doi.org/10.5281/zenodo.19349647

For b strands and n crossings, Theorems 1–2 give Hecke representation and
HOMFLY-PT computation using `O(b! b log b n)` ordinary operations and
`O(b! n)` algebraic operations, with at most `b!+O(1)` algebraic entries.
This is a different one-sided invariant backend, not a complete test.
Bit complexity still includes Laurent-polynomial degrees and coefficient
heights. Its factorial strand dependence can make it useful on moderate
braid index without being uniformly quasi-polynomial.

## 8. What openai/math actually contributes to this investigation

GitHub plugin inspection covered README.md, full CONTENTS.md, the
family-116 formalization scope and manuscript introduction, and the
directory of family 306. The catalogue at inspection contained 722
manuscripts in 372 families. README cautions that verification status
varies and that unformalized results may have issues.

- https://github.com/openai/math/blob/main/README.md
- https://github.com/openai/math/blob/main/CONTENTS.md
- https://github.com/openai/math/blob/main/lean/docs/116.md
- https://github.com/openai/math/blob/main/preprints/One-Rational-Matrix-Hitting-Point-for-Noncommutative-Formulas-September-24-2026/build/introduction.tex
- https://github.com/openai/math/tree/main/preprints/Purely-Cosmetic-Surgery-on-Knots-in-the-Three-Sphere-September-23-2026

No direct unknot-recognition/Khovanov-computation theorem was found in the
catalogue. Family 306's cosmetic-surgery claim is topologically adjacent
but supplies no recognition runtime bound. Family 116's proposed matrix
hitting points are an algebraic-compression analogy. The formalization
scope explicitly does not separately assert the division-free theorem's
polynomial bit-construction and O(ns²) matrix-dimension bounds.

The precise interface gap is substantive: even granting a polynomial
identity tester for a supplied small noncommutative formula, one still
needs a small exact representation of the relevant chain complex and an
algorithm for homological ranks. Free-algebra identity testing also does
not automatically respect the quotient by cobordism relations. Hence no
new topological complexity theorem should be inferred from that source.

## Recommended research priorities

1. Finish an exact scalar skein evaluator with independently checkable
   crossing order, frontier width, coefficient heights and closure
   conventions. It is useful immediately and exposes reproducible width
   data without claiming complete detection.
2. Pursue compact *decision* certificates (rank-one or cancellation
   witnesses) whose size is not constrained by total Betti rank. Test on
   the explicit 3-braid exponential-rank families before stating any
   general width bound.
3. Implement the treewidth-two structural algorithm as a complete class
   backend, with certified local reductions.
4. Prototype the July 2026 hierarchy data structures: boundary patterns,
   handle indices, normal coordinates, and compressed parallelity
   bundles. Record actual restarts and hierarchy depth. The key research
   problem is the global envelope, not merely fast terminal graph checks.
5. For a uniform quasi-polynomial theorem, replace a blanket low-width
   conjecture by a dichotomy: either find a cheaply certified obstruction
   or construct a bounded-complexity positive certificate. Wide torus
   knots show why the obstruction branch is necessary.

Citation note for the parent: to cite subagent web refs in the user-facing
answer, open the sources in the parent session first. The full-text pages
were returned with word limits of 200; retain concise source summaries
and keep proposed consequences explicitly identified as our reasoning.
