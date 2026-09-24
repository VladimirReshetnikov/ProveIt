# Source, novelty, and proof audit

## Repository pin and access

Repository: https://github.com/VladimirReshetnikov/Surreal

Revision: `bcac55ae6fd3f2b354e568ba1d2e94d496a2cc59`

The GitHub connector was used for repository reads. A separate attempt to clone
with the container failed because the container could not resolve the GitHub
host. The manuscript does not claim that a full clone or Lean build was obtained.
The root README was read on the default branch during initial reconnaissance;
the later directory and report reads used the pinned revision above.

## Repository content actually inspected

1. Root `README.md`.
2. `docs/README.md`, including the research-report catalogue.
3. `docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/README.md`.
4. `docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/10-nonlinear-rigidity-PROOF_AUDIT.md`.
5. `docs/surreal/omnific-diophantine-geometry/12-curve-logarithmic-SOURCE_AUDIT.md`.
6. `docs/surreal/set-sized-quotients-of-omnific-integers/README.md`.
7. `docs/surreal/omnific-groups-and-lattices/README.md`.

Directory and tree metadata were also queried. Some large connector responses
were truncated. The comparison is not an audit of every article or source file.
An exact-keyword repository search for `Mahler` returned no results; that absence
is not a certificate that no relevant result exists anywhere in the repository.

The holonomic guide and nonlinear proof audit were particularly important. They
identify the already-developed support calculus, finite initial polynomials,
active-degree escape, first-order nonlinear corner method, no-order-unit
higher-order rigidity, and the distinction between exact and residue indicial
roots. These ingredients are credited and reproved as needed, not advertised as
new discoveries. The whole 91-page article was not independently reviewed here.

## Primary external sources actually consulted

- Jason P. Bell, Michael Coons, Eric Rowland, *The rational-transcendental
  dichotomy of Mahler functions*, J. Integer Sequences 16 (2013), 13.2.10.
  https://cs.uwaterloo.ca/journals/JIS/VOL16/Bell/bell2.html
  https://arxiv.org/abs/1210.2070
  Author-hosted full PDF:
  https://ericrowland.github.io/papers/The_rational--transcendental_dichotomy_of_Mahler_functions.pdf
  The displayed page containing Lemma 6 was inspected. It explicitly establishes
  the classical complex entire-Mahler polynomial theorem; this is not claimed new.

- Kumiko Nishioka, *Mahler Functions and Transcendence*, LNM 1631 (1996).
  https://link.springer.com/book/10.1007/BFb0093672
  Publisher metadata and scope were consulted, not the complete book.

- Sonia L'Innocente, Vincenzo Mantova, *A factorisation theory for generalised
  power series and omnific integers*, Advances in Mathematics 442 (2024), 109513.
  https://arxiv.org/html/1710.07304v5
  Used for Hahn/Conway normal forms and the omnific support definition, not as a
  source of the polynomial-composition theorem.

- Yu. V. Matiyasevich, *Diophantine representation of enumerable predicates*,
  Math. USSR-Izv. 5 (1971), 1–28.
  https://www.mathnet.ru/eng/im1910
  https://doi.org/10.1070/IM1971v005n01ABEH001004
  Journal metadata and abstract explicitly identify the classical undecidability
  input. Its proof is not reproduced or claimed as new.

- Zhi-Wei Sun, *Further results on Hilbert's Tenth Problem*, Science China
  Mathematics 64 (2021), 281–306.
  https://arxiv.org/abs/1704.03504
  Final version v7, 28 January 2021. The abstract states undecidability over the
  integers in eleven unknowns. This published result is the external input for
  the fixed-degree-ten corollary. No claim about a current optimal variable
  count is made.

Also consulted for orientation: the user-specified Wikipedia page on surreal
numbers and the abstract of Bell–Coons, *Transcendence tests for Mahler functions*,
arXiv:1511.07530. Neither supplies a new theorem claimed in this manuscript.
Some broad web searches returned irrelevant results, which were not used.

## Proposed contributions and their status

1. Strict composition-weight polynomiality for a top product of linear
   differential transforms of f(P), compared with nonlinear combinations of
   lower-degree polynomial pullbacks, over arbitrary-rank Hahn fields.
2. The corresponding exact-resonance degree bound and finite coefficient locus.
3. Nonsingular dominant-matrix polynomiality and a component-degree bound.
4. The equation-specific linear omnific classification using classical Smith
   normal form and the already-known constant-term retraction.
5. An explicit Euler-projector realization of every rational affine hypersurface
   as an entire-solution locus with a prescribed ordinary degree bound.
6. The resulting undecidability subclass, including the fixed-degree-ten
   application of Sun's result.

These are presented as a proposed theorem package with written proofs. No
exhaustive priority search, independently refereed novelty assessment, or Lean
verification was performed. No claim is made to solve the general higher-order
nonlinear differential rigidity question, the critical-weight case, or a named
longstanding conjecture outside the explicitly stated class.

## Important proof checks

- Evaluation families are examined before cancellation.
- Cofinal weighted coefficient valuations imply strong Hahn summability.
- A second radius proves the converse entire-support criterion.
- Gauss values come from finite residue polynomials, not evaluation at X=1.
- Derivative scaling contributes minus r times the logarithmic radius to growth.
- Lower-shift operator terms are suppressed uniformly in the input series.
- The residue indicial polynomial is nonzero; characteristic zero makes its
  ordinary integer root set finite.
- Polynomial substitution has an injective monomial initial form at large radius.
- Integer convexity is proved without dividing an element of Gamma.
- Leading coefficient valuations are retained through a common reference radius.
- The strict weighted gap multiplies the superlinear growth term positively.
- Polynomial degree bounds use exact rather than residue indicial roots.
- Omnific-coefficient polynomiality is acknowledged as automatic from support.
- The universal encoder uses d = q + T + 2; merely taking d > max(q,T) would not
  give the stated uniform degree bound in every case.
- Multiplication by N! makes the Euler projectors integral, and powers of N!
  clear all coefficient normalizations in the encoder.
- Nonlinear finite coefficient reduction is explicitly distinguished from
  Diophantine decidability.

## Validation performed

Written proof development and internal review; 2,369 exact finite assertions;
LaTeX compilation; PDF rendering and layout inspection. The finite assertions
include rank-two finite-support initial forms, integer convexity, resonances,
Euler projectors, encoding identities, worked equations, and finite Smith
certificates. Exact version and group counts are in `verification.json`.

## Validation not performed

No proof-assistant verification of the new theorems, no independent peer review,
no full repository build, no exhaustive historical-source comparison, and no
algorithmic verification of all infinite Hahn supports or all valuation ranks.
The Python program is explicitly not a proof of those universal assertions.
