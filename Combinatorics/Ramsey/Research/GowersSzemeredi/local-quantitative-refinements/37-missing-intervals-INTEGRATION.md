# Integration plan

## Placement and status

Proposed destination:

`Combinatorics/Ramsey/Research/GowersSzemeredi/sharp-missing-intervals/`

Preserve the standalone manuscript initially. Add a research-index entry only after review. Do not redefine the existing Section 5 targets silently or mark new statements proved in `gowers-proof-status.json` on the strength of this manuscript. No repository writes were performed during preparation.

## Statement crosswalk

| Manuscript | Role | Existing interface |
|---|---|---|
| Lemmas 3.1–3.2 | Positive bandlimited gap certificate | New elementary trigonometric/algebraic layer |
| Theorem 7.1 | Circle and empirical-measure lower bound | Alternative to Fourier-tail truncation |
| Corollary 7.2 | Weighted finite-cyclic strengthening | `lemma_5_2` and collision-safe multiplicity argument |
| Theorem 2.1 | Exact optimum and equality measures | Independent sharpness layer |
| Theorem 8.1 | Critical geometric stability | New optional analytic layer |
| Theorem 8.3 | Stability of the full mass extremizer | New optional transport/moment layer |
| Theorem 9.1 | Recurrence conversion | Dirichlet approximation plus stated Weyl input |
| Corollary 9.3 | Explicit local exponent | `lemma_5_5`, using `lemma_5_3_holds` as an input |
| Corollary 9.4 | Integer short-step interface | Square-root recurrence auxiliary |

## Two independent proof tracks

### Lower-bound track

Formalize the explicit vector `w`, the path recurrence, and the autocorrelation coefficient identity. Prove that the normalized polynomial is at most the open-gap indicator and that all nonconstant Fourier coefficients are positive. Sum against arbitrary finite nonnegative weights. Derive the integer frequency statement and cast into `ZMod N` only after proving the frequency is nonzero modulo `N`.

This track does not require abstract measure existence, root finding, the positive-polynomial factorization appendix, or semidefinite duality. It is the shortest route to the useful improvement of Lemma 5.2.

### Sharpness track

Prove the supported trigonometric moment criterion, then the zero-sum path estimate and rank-one localizing-matrix positivity. Use moment rank to establish the exact number and location of contact nodes. Finally obtain uniqueness and the noisy-gap equality measures by Vandermonde injectivity.

## Required safeguards

- Use unnormalized Fourier transforms for the finite-cyclic comparison.
- Keep the factor `M/(N-M)` and the assumptions `1 <= M`, `2*M <= N` explicit.
- Handle total weight zero without normalization.
- Distinguish the open gap from the stronger original half-open exclusion.
- Count polynomial samples with multiplicity, following the existing repository correction.
- The recurrence proof changes the Dirichlet scale to `floor(T^k*s/4)`; verify that the Weyl input allows this denominator range.
- Retain integer square-root conditions and constant absorption in any partition application.
- Do not infer a global Szemeredi bound without a separate parameter propagation proof.

## Suggested theorem names (specifications only)

`gap_certificate_coefficients`, `weighted_missing_interval_linear_cutoff`, `first_window_moment_optimum`, `noisy_gap_mass_optimum`, `critical_grid_concentration`, `weyl_to_monomial_recurrence_optimized`.

These names are proposals, not declarations from compiled Lean code.
