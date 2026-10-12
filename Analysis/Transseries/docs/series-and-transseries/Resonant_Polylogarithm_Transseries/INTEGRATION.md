# Proposed ProveIt integration

No repository write or pull request was made. This document proposes placement
for the delivered files; it does not assert that integration has occurred.

## Suggested home

Place the package in:

    Analysis/Transseries/docs/series-and-transseries/Resonant_Polylogarithm_Transseries/

Add a cross-reference from the polylogarithm reports or manuscript research
index, following that tree's current intake process. The contribution spans
both areas, but its sharpest result is an exact-core inverse transseries.

## Suggested index entry

**Resonant Polylogarithm Transseries: Gamma Borel Kernels, Cyclotomic Order Jets,
and Sharp Dilogarithm Reversion** (22 pages; conventional proofs; finite exact
and numerical verification; not formalized). Gives subtracted Gamma kernels
for integer order derivatives, finite periodic digamma/DFT coordinates,
harmonic Bell jets, positive rational Laurent coefficients for the exact-core
inverse of `-Li_2(-exp(x))`, its exact convergence radius and unique dominant
fold, and the sharp physical threshold `y >= pi^2/4`, including absolute
endpoint convergence. Extends the radius proof to an interior quadratic
polylogarithm-feedback family. The generic inverse transport and arithmetic-
averaging defect are credited to existing work. Eight research directions;
bounded source audit; no global priority certification.

## Editorial separation

Keep Theorem 2.2 labeled as a reconstruction of the classical complete
Fermi–Dirac expansion. Keep the generic engine of Theorem 5.1 attributed to
`Nonlinear_Stokes_Transport_Logarithmic_Inversion`. Proposition 10.1 is an
illustrative restatement of a phenomenon already covered there. These are not
new general closure theorems.

The model-specific contribution should be reviewed as Theorems 6.1, 7.1, and
8.1 together: an exact coefficient formula alone would not prove the radius or
the sharp endpoint. The Gamma/periodic identities in Theorems 3.1, 3.2, and 4.1
can be reviewed independently. `theorem_map.csv` gives the precise mapping.

Keep the future-work boundary law visibly unproved. Do not turn the finite
verification record into a Lean or interval-proof claim. Preserve the numeric
pitfall note, especially when validating derivatives in the polylogarithm order.

## Rebuild and review

Run the verifier into a new `replay/` directory and compare numerical outputs
at their stated precision. PDFs and timing metadata need not be byte-identical
across platforms. The delivered payload uses LF line endings. Caution that
ordinary text output may use platform defaults on a replay; this is not a
mathematical difference. Recompile the single TeX source, review hyperlinks,
and independently check the positive-iteration and dominant-circle arguments
before promoting the results to a canonical accepted manuscript.
