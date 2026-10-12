# Joint coefficients: intake reconciliation, 12 October 2026

These are intake findings about scope and overlap, not an independent acceptance
of every analytic estimate. The complete delivered article and its evidence
remain unchanged. This source continues the parent report; it has no competing
base manuscript. No results are discarded or merged into a volume at intake.

## Current repository targets

The parent `sections/07-verification-research.tex`, lines 186–208, asks for
“Joint coefficient asymptotics as both the order and feedback vary.” Lines
209 onward ask for “Relative matching in expanding crossover windows.” The
new `sections/04-uniform-expansion.tex`, `thm:all-orders`, supplies a proposed
answer to the first question on compact real `(s-3) log(n)/2` windows and
compact positive feedback intervals. Its error is absolute and uniform in
the lattice location, with each truncation order fixed. The Fourier proof
uses positive compound-Poisson intensities for the outer contour and a finite
central expansion; it does not substitute a moving order into a fixed-order
asymptotic formula.

The positive-wing theorem in `sections/06-positive-wing.tex` addresses part
of the second question. It uses the absolute theorem at a sufficiently high
fixed order and additional kernel-tail bounds to obtain relative matching
for positive standardized locations up to each fixed power of log(n).
Negative growing windows and the maximal possible positive window remain
open. The exact scale selects B>1. Its endpoint normalization is not claimed
to be the actual coefficient radius on the interior-fold side.

The current collective manuscript's `chapters/01-lambert-moments.tex` already
contains the marginal Gamma-moment polynomials. The new source's identity
`D_j = Q_j(-log 2)` reconciles the normalization and does not establish first
derivation of those polynomials. Its positive analytic composition theorem
requires nonnegative coefficients and a common analytic endpoint margin.

## Reciprocal endpoints overlap an existing continuation

The local classification in `sections/07-reciprocal-endpoints.tex` duplicates
the conclusion `ep:thm:classification` of
`Resonant_Lambert_Inverse_Transseries/continuations/summation-singularities/sections/endpoint.tex`:
for noninteger s-1=p/q the minimal ramification is min(p,q), with the
unramified family s=1+1/q, q>=2. Preserve both attributed proof routes.
The joint source additionally supplies a convergent moving-order reciprocal
chart. Local endpoint removability does not determine the global Taylor radius.

The direct-inverse predecessor's question 9 is at
`Polylogarithm_Resonance_And_Inverse_Transseries/polylogarithm_resonance_and_inverse_transseries.tex:1898`.
Both continuations identify a local obstruction to an all-real-order extension
of its integer cut-modulus inequality for 1<s<3/2. Neither refutes the printed
integer theorem or resolves the full global question. No retraction is warranted
by this comparison. The delivered proposed status paragraphs remain proposals
pending statement-level analytic review and canonical incorporation.

## Fresh replay

All three supplied verification programs completed at their default sizes on
an isolated copy with Python 3.13.14, NumPy 2.3.5, SymPy 1.14.0 and mpmath 1.3.0.
The fresh records and captured output are in `intake-verification/`.
They include the exact degree-eight original-equation identity, six finite
Stirling identities, 36 central Gamma identities, five marginal identities,
nine noninteger Fourier comparisons, the 36-case coefficient grid through
n=4096, nine reciprocal-endpoint and six cut-bank diagnostics.
Numerical comparisons are not interval certificates; none proves a uniform
analytic remainder. No claim of Lean formalization is made.

To reproduce, copy this directory outside the repository and run each of
`code/verify_coefficients.py`, `code/verify_symbolic.py`, and
`code/verify_endpoints.py` using `uv run --no-project` with the pinned packages
above. The scripts overwrite the copy's `data/`. The authored PDF is retained;
no source changes or volume rebuilds are part of this reconciliation.
