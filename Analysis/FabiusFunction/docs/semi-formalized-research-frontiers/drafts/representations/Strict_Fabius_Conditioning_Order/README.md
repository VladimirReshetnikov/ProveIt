# Strict Conditioning Order for Fabius Observation Masks

This five-page companion proves strict total-variation ordering when a larger observed cap replaces a smaller one, comparing an original uniform product conditioned below a threshold with a common exponential tilt. Positive summable caps, arbitrary real tilt, positive-probability conditioning, and finite/countable common observations are allowed, even when no hidden coordinates remain.

For one exchange, equality occurs exactly for equal caps, or zero tilt with vacuous conditioning. For finite masks of equal size admitting a cap-dominating matching, equality in the nontrivial model occurs exactly when the cap multisets agree.

In the Fabius convention, this gives overlap_late < overlap_early for every 0<q<1, rho>0, n>=2 and 1<=m<n, including arbitrary common outside observations. The names refer to the hidden blocks; the late-hidden mask observes larger caps.

## Contents

- `strict_fabius_conditioning_order.pdf`: complete report
- `strict_fabius_conditioning_order.tex`: editable LaTeX source
- `build.sh`: ordinary three-pass TeX Live build
- `checks/verify_strictness_exact.py`: Python standard-library exact rational checker
- `checks/strictness_exact.json`: 98,956 strict-level comparisons, 396 normalized affine profiles and the exact generic equality counterexample
- `SOURCES.md`, `validation.json`, `SHA256SUMS`: source context and artifact verification

Run `python3 checks/verify_strictness_exact.py` for the regression checks and `bash build.sh` to rebuild the PDF. The mathematical proof, not finite testing, establishes the universal statements.

This is a fixed-conditioning comparison. It does not assert one kernel for all weights, strictness for every divergence generator, or unrestricted noise extensions. The companion leaves preceding reports unchanged. It makes no worldwide priority claim and is neither formally verified nor externally refereed.
