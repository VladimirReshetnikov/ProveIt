# Source and novelty audit

## Repository

Repository: https://github.com/VladimirReshetnikov/Surreal

Working branch snapshot returned by the GitHub connector:
`9ee2dac0d234c90415f6b7290cbe5b4dcf4a4d3e`.
The returned commit timestamp is 2026-09-24T00:25:54Z; the manuscript uses
“September 2026” rather than treating that UTC date as a conflicting local date.

Directly consulted through the connected GitHub tools:

1. Root directory metadata and the root README at the then-current main branch.
2. `docs/README.md` at the then-current main branch.
3. `docs/surreal/set-sized-quotients-of-omnific-integers/README.md` at main.
4. `docs/NOTATION.md` at the pinned commit.
5. `docs/surcomplex/analysis/README.md` at the pinned commit.

Pinned guide URLs:

https://github.com/VladimirReshetnikov/Surreal/blob/9ee2dac0d234c90415f6b7290cbe5b4dcf4a4d3e/docs/NOTATION.md

https://github.com/VladimirReshetnikov/Surreal/blob/9ee2dac0d234c90415f6b7290cbe5b4dcf4a4d3e/docs/surcomplex/analysis/README.md

The guides were used to identify conventions and avoid the already extensive
omnific quotient/Diophantine/automorphism program. A complete repository clone
was not available through the container network. No exhaustive source-code,
Lean-build, or full-manuscript review is claimed. The main dynamical proofs
are independent of unreviewed repository research claims.

## Primary mathematical sources checked

### Karl-Olof Lindahl

“Linearization in ultrametric dynamics in fields of characteristic zero —
equal characteristic case,” p-Adic Numbers, Ultrametric Analysis and
Applications 1(4) (2009), 307–316.

https://arxiv.org/abs/1111.1993
https://arxiv.org/html/1111.1993v1
https://arxiv.org/pdf/1111.1993
https://doi.org/10.1134/S2070046609040049

Checked role: Theorem 1.1 (rank-one linearization disk bounds), the formal
Schröder recursion, and Lemma 3.3 (root-of-unity small-divisor dichotomy).
The HTML text and relevant PDF page images were inspected. These ingredients
are credited as existing work, not presented as new results.

### Bjorn Poonen

“Maximally complete fields,” L'Enseignement Mathématique 39 (1993), 87–106.

https://math.mit.edu/~poonen/papers/amsval.pdf

Checked role: the Hahn/Mal'cev–Neumann field construction and Corollary 4
(PDF page 10), which gives algebraic closedness for a divisible value group
and algebraically closed coefficient/residue field. Only this standard input
is needed for factoring the finite polynomials in the article.

### David Marker

“Model Theory of Valued Fields,” Math 512 lecture notes, UIC, Fall 2018.

https://homepages.math.uic.edu/~marker/math512-f18/valued_fields_1-2.pdf

Checked role: Lemma 2.36, Neumann's positive-support lemma, including the
variable-length finite-word finiteness statement. The page image at PDF
page 23 was inspected because parsed mathematical text was imperfect.

### Orientation only

https://en.wikipedia.org/wiki/Surreal_number

The user-supplied overview was read for context. No proof depends on it.

## Proposed contribution boundary

The following exact combined formulations are proposed contributions of this
draft, with proofs in the article:

- The arbitrary-rank common-support proof and sharp coefficientwise
  linearization threshold for the finite equivariant polynomial family.
- The joint periodic-divisor / boundary-vector-field invariant.
- Its explicit algebraicity test and specialization-based transcendence
  certificate for the full conjugacy.
- Exact finite shell realization and its omnific reciprocal-map consequence.

Neumann's lemma, Hahn algebraic closedness, the formal recursion, the
small-divisor dichotomy, polynomial iterate divisibility as an algebraic
mechanism, and the norm/logarithmic-derivative argument are not claimed as
new general mathematics.

Targeted searches did not locate a primary source with the entire formulation,
but some broad queries returned poorly targeted results. That is not evidence
of a universal absence. Further expert literature review is needed before any
priority claim. The paper makes no assertion that a named longstanding open
problem has been resolved and does not claim an independently certified
“breakthrough.”
