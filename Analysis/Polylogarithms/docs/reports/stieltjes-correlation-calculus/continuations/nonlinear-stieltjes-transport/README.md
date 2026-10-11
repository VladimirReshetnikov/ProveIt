# Nonlinear Stieltjes Transport

**Finite-part cocycles, harmonic contact terms, Möbius averages, and exact polylogarithmic identities**

Research continuation prepared for Vladimir Reshetnikov, ProveIt, 10 October 2026 (Pacific time).

## Reading

`article.pdf` is the complete article; `article.tex` is its editable source. It includes the analytic proofs, precise normalizations, explicit ordinary convergent identities, targeted source audit, and further research programme.

The principal results are an all-logarithmic-power coordinate-change formula for Hadamard finite parts, its all-index Stieltjes specialization, a sharp tangent-coordinate vanishing law, transport of existing collision contact distributions, and an all-index family of nonlinear circle averages. Odd-order polygamma averages reduce to rational functions times powers of pi. The primitive hierarchy supplies an ordinary log-Gamma average and positive-order polylogarithmic formulas.

The article uses the sign convention `gamma_0(x) = -digamma(x)`. A superscript `(p)` on `gamma_m` is an argument derivative; `[j]` on `Li_s` is a spectral/order derivative. Finite parts use a cutoff in the named coordinate at scale one. Density pullback and unweighted composition averages are kept distinct.

## Verification

```sh
python -m pip install -r requirements.txt
python code/exact_checks.py
python code/numerical_checks.py
python code/build.py
python code/inspect_pdf.py
python code/verify_manifest.py
```

The exact suite records **504 passing rational/polynomial assertions**, including an independent cutoff-antiderivative implementation, composition checks, Lagrange delta transport, harmonic singularities, a negative control, and the sharp vanishing threshold.

The numerical suite records **47 passing high-precision comparisons** at 70 decimal digits. The maximum delivered scaled residual is approximately `1.407e-63`, below the configured tolerance `1e-43`. These are diagnostics, **not interval certificates or proofs**. Local Taylor degree, endpoint switch, series length and per-test residuals are in `data/numerical_checks.json`. The degree-42 near-endpoint expansion is a numerical stabilization device, not a certified remainder bound. The numerical suite takes roughly one to two minutes on the delivery environment; runtime varies.

The article build requires `pdflatex` with standard AMS, Latin Modern, geometry, microtype, hyperref and fancyhdr packages. The optional inspection script requires Poppler (`pdftoppm`, `pdftotext`, `pdfinfo`). No network access or external datasets are needed after installing dependencies. Regeneration changes run-time metadata and can change PDF bytes, so checksums identify the delivered snapshot rather than all possible rebuilds.

## Integration and scope

`INTEGRATION.md` proposes placement. `integration/manuscript_insert.tex` is a standalone mathematical insert with namespaced labels; `integration/insert_driver.tex` is a minimal compilation wrapper. These files do not modify the live repository.

`SOURCE_AUDIT.md` records the observed repository revision, actual reading scope and matching Git blob hashes for two incoming archives obtained from the Library. `CORRECTIONS.md` distinguishes proposed safeguards from genuine errata: no error is asserted in the correctly scoped fixed-coordinate no-lower-contact theorem.

General regularization-change theory and the classical Hurwitz/Gamma inputs are credited in the article. No exhaustive global novelty search, numerical period-independence theorem, proof-assistant formalization, solution of the remaining S6 question, or full simultaneous collision-diagonal theorem is claimed.

`SHA256SUMS` identifies all delivered files except itself. Temporary LaTeX files, render images and original incoming archives are intentionally not included.
