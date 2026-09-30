# Sources and comparison audit

Audit date: 29 September 2026 (Pacific date).

## Repository snapshot and target

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned README snapshot: e1afd75e35a4de734d5aa47aec5cdb917b82ed3e

Relevant directory:

    SetTheory/Cardinals/docs/reports/hankel-determinants/catalan-and-ballot/
    shifted-catalan-hankel-polynomials/

(The line break above is for readability, not part of the path.)

The GitHub connector was used to inspect repository search results and the
pinned README. That README describes three merged parts: the shifted linear
multiplier, arbitrary polynomial multipliers and fixed-root sectors, and a
single-root cyclotomic classification. The repository's search index and its
live tree were not assumed to be the same snapshot. This was a targeted source
inspection, not a full clone or a complete audit of all incoming articles.

The moving-root question was checked in the standalone source manuscript
*Root Collisions and Sharp Recurrences for Polynomially Weighted Catalan Hankel
Determinants* (28 September 2026), available in the user's file library. Its
subsection “Uniform endpoint and root-collision limits” corresponds to Section
24.4 in the combined repository report. It asks for uniform limits and errors
at endpoints, and separately for two nonendpoint roots approaching at order
N^(-1). The present article answers the nonendpoint fixed-degree version.

The library source used for that exact question was named:

    article(20260929-023936).tex

A later library manuscript, *Two-Endpoint Confluence for Catalan Hankel
Determinants: An exact even finite-size expansion, the first interaction law,
and a sharp critical scale* (29 September 2026), was inspected at the relevant
scope and research-question sections. It explicitly leaves the nonendpoint
problem to Section 13.1 and asks for a uniform oscillatory-sector counterpart.
Its source was named:

    article(20260930-010250).tex

Its PDF was named article(20260930-010248).pdf. The UTC upload timestamps in
these filenames are not the manuscript's Pacific-date heading. These files
were read through Files, not inferred from filenames. They are not redistributed
in this package.

## Public primary literature

1. Christian Krattenthaler, *Hankel determinants of linear combinations of
   moments of orthogonal polynomials, II*.
   https://arxiv.org/abs/2101.04225 (v5, 10 September 2021).
   Ramanujan Journal 61 (2023), 597–627.
   Theorem 1, the confluent discussion, and recurrence context are the classical
   comparison. The abstract, PDF text, and a rendered theorem page were inspected.
   No novelty is claimed for the underlying polynomial-modification identity,
   confluence principle, or general recurrence framework.

2. Eugene Strahov and Yan V. Fyodorov, *Universal results for correlations of
   characteristic polynomials: Riemann–Hilbert approach*.
   https://arxiv.org/abs/math-ph/0210010
   Communications in Mathematical Physics 241 (2003), 343–382.
   The primary abstract describes determinant formulas for products and ratios
   of characteristic polynomials in terms of integrable orthogonal-polynomial
   kernels, and their universal asymptotic structure. This is credited as broad
   prior context, not used as an unproved theorem in the new derivation.

3. Andrew F. Celsus, Alfredo Deaño, Daan Huybrechs, and Arieh Iserles,
   *The kissing polynomials and their Hankel determinants*.
   https://arxiv.org/abs/1504.07297
   https://doi.org/10.1093/imatrm/tnab005
   Transactions of Mathematics and Its Applications 6 (2022), tnab005.
   The primary abstract was found through indexed arXiv results; later indexed
   excerpts of the author-uploaded paper on ResearchGate included the moment
   determinant, the cube-vertex integration-by-parts method, and parity
   asymptotics. Direct arXiv PDF and publisher page retrievals were unsuccessful.
   Accordingly, a complete theorem-by-theorem comparison with that paper was
   not performed. The article explicitly makes no novelty claim for the
   oscillatory Jacobi determinant, even/odd nondegeneracy phenomena, or
   large-frequency kissing-point analysis. Its versions are independently
   proved for the normalization required here.

## What the audit does and does not establish

The present manuscript is a proof-focused repository continuation, not an
exhaustive historical survey. Targeted searches included Catalan Hankel root
collisions, characteristic-polynomial bulk limits, centered determinant
expansions, and oscillatory Jacobi/kissing Hankel determinants. Finding the
kissing-polynomial literature led to an explicit restriction of novelty claims.

The leading profiles, sine-kernel identities, and classical parity laws are
not claimed as discoveries. The contribution relative to the inspected reports
is the collision-uniform convergent amplitude construction, its explicit first
coefficient and compact Cauchy bound, the separated-cluster constants, and the
convergent phase-dependent finite-size zero expansion. A bounded audit cannot
certify worldwide priority for every coefficient or corollary. No theorem from
the unrefereed source reports is needed as an unproved premise in the new proofs.
