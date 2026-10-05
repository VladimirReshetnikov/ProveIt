# Reader verification: order-seven B-tree histories (A336009)

This directory is a self-contained finite verification suite for the accompanying report. It does not contain the source papers or private research notes. Python 3.10 or later is required; the replay was tested with Python 3.12, SymPy 1.14.0 and mpmath 1.3.0. The latter is only used for the optional numerical fit.

## Run

From this directory, with the dependencies in `requirements.txt` installed:

```sh
python -B check.py
python -B -O check.py
python -B validate_bundle.py --with-exploratory --output /tmp/order7-validation.json
python -B exploratory_fit.py --output /tmp/order7-exploratory.json
```

`check.py` emits a JSON result and exits 0 on success, 1 on a named check failure, and 2 on an unexpected exception. Every substantive guard uses an explicit conditional, so optimization mode cannot turn the guards off. It checks the strict file manifest before mathematical checks. `--skip-integrity` is a development option and is not a sealed-bundle verification.

The tools do not overwrite their inputs. Output paths must be outside this directory. Python may create its usual `__pycache__`, which is excluded from the integrity manifest; the replay harness disables bytecode generation. The suite needs no network access after installation.

## Exact fixtures and finite checks

- `fixtures/oeis_A336009_prefix.json` contains precisely the 31 displayed OEIS terms, indices 0–30, rechecked at https://oeis.org/A336009 on 2026-10-02. No external 501-term table is claimed
- `fixtures/recurrence_terms_0_500.txt` freezes 501 generated exact integers. One computation uses the integer/binomial recurrence; a second computes rational ordinary Taylor coefficients of the EGF by squaring and integrating four times, then multiplies by factorials
- `fixtures/reference_formulas.json` contains selected exact constants and coefficients from the report. Coefficient pairs `[r,s]` mean `r+s sqrt(-159)`, with rational strings and no floating-point conversion
- Exact checks cover the pole coefficient 840, EGF coefficient 140, rational comparison certificates, Fowler polynomial and normalized derivatives, indicial factorization, three stable eigenvectors and the chart determinant, nonresonance bound and Catalan constant, and a three-variable expansion through total degree 5 (56 monomials including zero), its polynomial PDE, and conjugation
- The energy derivative identity, coefficient −3008678400 c0, exact c0, D(24), scalar-majorant bound, radius fraction 35/1066, and final contradiction bound 169/175 are checked exactly. Ten scalar coefficients are checked against their Catalan majorant
- Finite transfer identities check the factor 6 and polynomial sectors. Four inverse-power gamma coefficients are checked both by Bernoulli-polynomial recursion and by the exact gamma shift equation. The inverse scale/shift and Lambert corrections through the third inverse power are checked by formal residual substitution and an independent Taylor expansion

These calculations do not prove the analytic claims by finite sampling. The report supplies the real blow-up theorem application, continuation/gluing, convergent stable surface, actual-orbit argument, nonvanishing of the complex amplitude, transfer hypotheses, and inverse error estimates. Finite algebra checks also cover the two corollary models: pure-axis recurrences, exponent-uniqueness identities, the polynomial degree obstruction in sample degrees, an actual collision requiring grouped exponents, and the factorial/EGF recurrence operator. These do not certify infinite monodromy or non-D-finiteness; the corollary gives the infinite and analytic arguments. The suite does not certify literature priority or any decimal digit of an asymptotic constant.

## Package-wide manifest

`python -B check_manifest.py .. --write` generates the package-wide `CHECKSUMS.sha256` after the publisher has finalized all package files. `python -B check_manifest.py ..` verifies it. It is a strict closed inventory of every ordinary file other than itself, including this suite’s JSON manifest. Duplicate or unsafe paths, symlinks, special files (such as FIFOs), wrong digests, missing files, and unlisted files fail explicitly. Unlike the suite-only manifest, it has no cache exclusions; use `-B` and remove caches before sealing the full package. Readers should verify rather than rewrite the supplied manifest.

## Integrity and negative tests

`MANIFEST.json` records the SHA-256 of every distributed file in this directory other than itself. Missing, modified, and unlisted files are errors; duplicate keys and malformed fixture types receive explicit named diagnostics. The manifest detects changes, not adversarial replacement of both data and checks.

`validate_bundle.py` executes normal and optimized checks, compares their outputs, replays from a fresh temporary directory, records all source-file hashes before and after, and requires that the source hashes remain unchanged. It then makes 15 deliberately bad copies and requires a specific diagnostic in both normal and optimized mode, for 30 negative runs. It also tests the package-wide manifest on ten independent mutations (20 normal/optimized runs), including an unlisted bytecode cache, unsafe paths, duplicate entries, a symlink, and a FIFO. An unexpected exception is a failure of the harness, never a successful mutation test. Semantic-fixture mutations deliberately reseal the temporary checksum table so the algebra and schema checks, rather than only file hashes, must detect them. The three integrity mutations do not reseal.

## Optional exploratory fits

`exploratory_fit.py` uses 100-decimal mpmath point arithmetic and degrees 1–4 of the gamma-ratio model. It fits rho and the real/imaginary parts of C to four triples of exact terms, with the real stable amplitude fixed by the exact energy identity. `fixtures/exploratory_reference.json` records the reproduced output and explicitly identifies residuals at indices used to fit the model.

The result status is `EXPLORATORY_ONLY`, separate from the exact checks. The harness's optional `EXPLORATORY_REPRODUCED` result means the point computation was reproduced, not that its numerical error or displayed digits were certified. The fitted constants, stable digits, small residuals, and apparent numerical C != 0 are not inputs to the proof. A separate analytic majorant argument establishes C != 0.
