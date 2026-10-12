# Suggested ProveIt integration

No repository files have been changed. A suggested new report location is:

`Analysis/Polylogarithms/docs/reports/rational-hankel-polylogarithms/`

The directory name is a proposal, not an assertion that it already exists. Preserve the standalone article, its exact verification code, data, claim-status file, and source audit together. `summary.tex` is a short optional manuscript bridge, not a substitute for the complete proofs.

## Source conventions

The article uses nodes `1,...,M`. The adjacent-pole source uses `0,...,N`; translate with `M=N+1`, `n_source=n-1`, and `a_source=a+1`. A monic change of polynomial basis has determinant one. In particular, the source's shifts 1 and 2 correspond to this article's shifts 0 and 1.

The formal harmonic weight is not the previously established ordinary harmonic degree. The weighted bound does not prove minimal transcendental weight or minimal depth. No evaluated-constant independence claim is needed.

## Status updates

Theorem references in the bridge use prefixed labels `rhp:`. On intake, link the complete report rather than duplicating all formulas in several chapters.

For gap-six Questions Q7–Q9, record the finite compiler, the integral-quadratic-denominator dilogarithm corollary, the normalized fixed-size top coefficient, endpoint jet equations, and spectral Euler identities. Keep intrinsic cancellation thresholds and minimal classical-depth classification open. The unrestricted moment-prefix conjecture, S6, and revised S8 remain untouched.

For gap-six Q4, cross-reference the separate Gamma-normalization package, not this report's unrelated Hahn norm products. The two uses of Gamma normalization are mathematically different.

Replay `python verify_all.py` and build the PDF before changing the host manuscript's accepted-result status. The supplied exact tests are not a Lean or other proof-assistant certificate. Apply the project's normal proof-audit and attribution policy.
