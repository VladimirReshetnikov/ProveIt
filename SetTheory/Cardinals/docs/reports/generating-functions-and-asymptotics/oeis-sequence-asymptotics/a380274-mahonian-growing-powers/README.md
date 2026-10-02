# Growing powers of Mahonian coefficients

This package proves a growing-power extension of Mahonian collision sums. It does not claim a new fixed-power result for OEIS A380274 or A380275.

## Results

- For every r_n tending to infinity, an exact-modal-normalized theta equivalent, including both neighboring regimes
- Parity-sensitive transition at r_n comparable to the inversion variance, of order n^3
- Exact adjacent-ratio first-shell asymptotics for arbitrarily fast growing powers
- Uniform arbitrary finite expansions on compact positive transition scales, with an explicit fourth-order formula
- An unnormalized multiplicative equivalent retaining the quadratic and linear exponential corrections
- Conditional common-inversion Gaussian, discrete-Gaussian, and modal limits
- A fixed-critical-path Lambert-W inverse, plus explicit higher-order real asymptotic models and a separate discussion of discrete thresholds

The PDF is the main report. The TeX is editable. The literature report identifies established fixed-power work, related local-curvature methods, and discrete Gaussian and entropy prior art. Novelty remains provisional; this is not a peer-reviewed publication or a formal proof-assistant certificate. No full beyond-all-orders transseries is claimed.

## Files

- `mahonian_crossover.pdf`, `mahonian_crossover.tex`: report and source
- `derive_coefficients.py`, `coefficients.txt`: exact rational weighted-Fourier coefficient calculation
- `check_crossover.py`: exact integer coefficient recurrence with high-precision evaluations
- `numerical_checks.json`: 30 critical-window cases, n through 322
- `endpoint_checks.json`: 30 subcritical and supercritical checks
- `unnormalized_checks.json`: 30 checks of the explicit multiplicative equivalent
- `audit_independent.py`, `audit_independent_results.json`, `audit_symbolic.txt`: independent Hermite-polynomial calculation, odd-n recurrences through 483, and inverse checks
- `audit.md`: independent mathematical review with the audited TeX hash
- `literature.md`: primary-source boundary and remaining uncertainty
- `build.sh`: portable PDF rebuild, including local TeX cache bootstrap where necessary
- `verify.sh`, `verify_results.py`: computational replay and regression checks
- `quality_receipt.json`, `provenance.json`, `SHA256SUMS`: release checks and provenance

## Reproduce

Use Python 3 with SymPy and mpmath installed. Run `sh verify.sh` from any working directory. All generated files are written beside the scripts. The independent checker asserts the exact rational curvature coefficients and bounds each numerical reference tail below 10^-75 using log concavity. The numerical regression checks are consistency checks, not substitutes for the analytic proof.

To rebuild the PDF, use `sh build.sh` with a TeX distribution containing the listed standard packages. The script installs nothing and keeps generated caches inside the package. A rebuilt PDF may differ byte-for-byte because of its creation timestamp; the mathematical source hash is the audit anchor.

The inverse formulas use the explicitly fixed path r_n = rho V_n. For the simple Lambert correction, eventual nearest-integer recovery applies to exact index inputs; no certified finite onset is supplied. Arbitrary threshold queries require checking neighboring allowed integer candidates or certified error envelopes.
