# Source and proof audit

Date: 23 September 2026.

## Repository snapshot and actual inspection

Repository: https://github.com/VladimirReshetnikov/Surreal
Commit: `9693b28c24e6fcb317ce47969a40185c5dfef402`.

Read using the connected GitHub tool:

1. Recursive tree at the pinned snapshot; root README.
2. `docs/README.md`, the catalogue of 51 reports.
3. `docs/new` directory tree (only its procedural README at this snapshot).
4. `docs/surreal/euclidean-three-space/` directory listing.
5. `docs/surreal/euclidean-three-space/README.md`, its detailed guide, especially
   the provenance and theorem inventory for the rotation and quotient work.
6. `docs/surreal/euclidean-three-space/10-rotation-quotients-SOURCE_AUDIT.md`,
   read in full.

A local clone attempt failed because the execution environment could not
resolve its proxy. There was no successful local repository build. The
306-kilobyte integrated article.tex was not fully read. The full 96-page
predecessor and all other reports were not line-by-line audited. The comparison
is expressly targeted; repository theorem claims come from the actual guides
and source audit, not invented inspection of unseen Lean files.

## Prior results explicitly not claimed as new

The repository predecessor already develops the SO(3) valuation-cut calculus,
normal closures, mixed single-commutator images, perfect residuals, a universal
set-sized quotient, SO(n)/SU(n) extensions, and the circle/U(n) boundary.

The present article gives an independent Nash-submersion proof applicable to
all compact simple Lie algebras. It does not claim the earlier classical
matrix cases, central decomposition, infinitesimal logarithm, or ordinary
signed-permutation classification as new discoveries.

## Primary literature inspected

- Alessandro D'Andrea and Andrea Maffei, *Commutators of small elements in
  compact semisimple groups and Lie algebras*, Journal of Lie Theory 26 (2016),
  683-690. Local commutator openness is a precedent, not a result originated
  here. Primary PDF (including visual inspection):
  https://www.heldermann-verlag.de/jlt/jlt26/andla2e.pdf

- Martin Bays and Ya'acov Peterzil, *Definability in the group of infinitesimals
  of a compact Lie group*, Confluentes Mathematici 11(2) (2019), 3-23,
  DOI 10.5802/cml.58. The infinitesimal central/semisimple decomposition and
  valued-field interpretability are prior results. Section 5, Fact 5.3 and
  Claims 5.4-5.5 were inspected explicitly.
  https://cml.centre-mersenne.org/item/10.5802/cml.58.pdf
  https://arxiv.org/html/1901.10831v4

- Linus Kramer, *On small abstract quotients of Lie groups and locally compact
  groups*, arXiv:1405.2711v3 (2016). Its discussion of quantitative normal
  generation, including Nikolov-Segal's Theorem 6.11, is an important prior
  context. Its ordinary/countable small-target issues are not identified
  with this article's proper-class/all-set question.
  https://arxiv.org/html/1405.2711v3

- Olivier Bournez and Quentin Guilmant, *Surreal fields stable under
  exponential and logarithmic functions*, arXiv:2201.08199. Normal forms,
  coefficientwise arithmetic, the Hahn realization, and the near-one
  logarithm were checked in the current PDF. The normal-form/Hahn page was
  also inspected as a PDF image.
  https://arxiv.org/pdf/2201.08199

Publisher records were checked for Gonshor's 1986 book, Conway's 2001 second
edition, and Bochnak-Coste-Roy's *Real Algebraic Geometry* (1998). Those books
are background references; no claim of a full reading during this task is
made. The Nash inverse-function transfer used in the paper is explained in
its own finite-dimensional lemmas.

## Candidate contribution and priority boundary

The main candidate-original result is the exact small-observation theorem
for every compact connected real algebraic group evaluated in No:

- The elements killed by every set-sized group homomorphism are exactly
  mu_S = [mu_G,mu_G].
- An explicit separating class quotient is G(R) x mu_Z.
- A universal set-sized quotient exists precisely when the connected central
  torus is trivial, equivalently when G is semisimple.

The normal-generation proof and valuation-cut product classification supply
a uniform all-type route. No identical all-compact-group statement was found
in the inspected sources, but this is not an exhaustive priority search.
Nothing is advertised as a certified historical breakthrough or as a solution
to a named published longstanding open problem.

## Proof-sensitive points

The article checks explicitly the following potential failure points:

1. The normalized word maps extend as Nash maps after division by a or ab.
2. The needed existence statement transfers as a finite first-order statement,
   not as a completeness or convergence assertion.
3. An ordinary finite root and a finite power enlarge the real output ball
   to a full valuation ball. No infinite word length is used.
4. A collision argument always runs on one set larger than the target, using
   scales in a prescribed positive surreal interval.
5. Simple-factor normal generation is not applied directly to a torus or to
   an element supported in just one of several semisimple factors.
6. The mixed-depth theorem concerns the generated commutator subgroup, not
   the image of a single commutator map.
7. The class quotient is given by explicit set-coded pairs, not a collection
   of proper-class cosets.
8. Coefficient maps separate the central infinitesimals; they are not asserted
   to exhaust the abstract algebraic dual.
9. Conway monomials t^gamma = omega^(-gamma) are not confused with arbitrary
   surreal powers defined using a global exponential.

## Computational and editorial verification

All 33 named exact finite checks in verify.py passed. They cover SL2 matrix
identities, so(3) and su(3) bracket-spanning certificates, a mixed Cayley
commutator derivative, finite logarithm identities, and small monomial-matrix
counts. Full data, including nonzero certificate determinants, is included
in verification_results.json.

These are not a formal verification of the general theorems. No Lean build,
proof-assistant certificate, or independent referee review was performed.
The PDF was compiled successfully, cross-references stabilized, final LaTeX
warnings checked, and rendered pages visually inspected.
