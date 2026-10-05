# Finite-checker validation audit

2 October 2026. **Result: PASS; no unresolved defect found in the finite mathematical checker.** This audit concerns exact finite calculations and validation guards. It neither certifies the analytic asymptotic proof nor infers an asymptotic theorem from numerical agreement.

## Mathematical implementation

The pristine `check.py` passes in ordinary Python and with `python3 -O`: **17,643 checks**, followed by exact agreement with all four fixtures. Mathematical operations use integers and `fractions.Fraction`; no floating-point literals, approximate tolerances, or removable `assert` guards are used.

The following formulas and domains were inspected and exercised:

- The direct binder/application/abstraction recurrence and an independently arranged size recurrence agree for both variable-size conventions at sizes 0–30, including the size/parity conversion and 22 published-prefix entries
- Shape dynamic programming through 16 unary vertices agrees with the Catalan/binomial formula; explicit shapes through seven unary vertices check leaf/internal counts, depths, height deficit and agreement with the height distribution
- The height-refined radical recurrence agrees with the direct recurrence for 1–8 unary vertices and 0–9 applications, including the zero-application boundary
- Coarse and height-sensitive radical inequalities are checked after squaring their positive factors, so all comparisons remain rational; the height tests use three exact rational values of delta
- The spine coefficients are formed by exact truncated convolution for 1–10 unary vertices and 0–28 applications; both subclass inclusion and the Catalan-convolution lower bound are checked
- Negative-binomial means and the variance bound are checked for 1–100 unary vertices; the independent probe additionally derives component variances from the first two probability-generating-function derivatives and verifies the summed harmonic-number identity

Forward reversion through order eight uses two genuinely different coefficient identities: a logarithmic power expansion, and `U exp(S)=1` with exponential coefficients obtained from `E'=S'E`. Inverse reversion through order six, for both size conventions, uses the split logarithmic identity and `(U^2+A x U+x^2) exp(S)=1`. These routes intentionally share elementary exact polynomial arithmetic; “independent” here does not mean independent arithmetic libraries or proof implementations. Residual identities and the printed coefficients are also checked.

`validation/auditor_probes.py` provides a further separately coded scalar implementation: logarithms from the derivative/reciprocal identity, exponentials from factorial-weighted powers, and inverse reversion using the single logarithm of the quadratic core. It passes **77 exact series comparisons** at eleven substitutions, alongside the probability-generating-function moment checks, in both Python modes.

## Failure detection and preservation

The independent probes inject **16 mathematical equation/sign/index faults and nine fixture faults** into temporary copies. Every case fails at its specified mathematical or fixture guard in both Python modes. Mathematical mutants run the checker directly, without a manifest check, so a generic hash failure cannot substitute for a live mathematical guard. The tests cover malformed and duplicate-key JSON, changed values, booleans or floats substituted for integers, missing/extra files, an extra directory and a fixture symlink. Checker and fixture SHA-256 values are unchanged before and after each complete probe run.

The packaged corruption campaign was also run independently in disposable package copies. Its **34 cases produce 68 rejections** per run, and the campaign itself passes with and without optimization. It checks pristine integrity and mathematics first, requires named mathematical diagnostics and file-specific payload-corruption diagnostics, and verifies before/after hashes of the original copied payload and manifest. Additional normal/optimized tests rejected malformed hash strings, noncanonical manifest paths, invalid size types and payload symlinks. The final intact copy again passed strict inventory verification.

The inventory checks exact relative filenames, sizes and SHA-256 values, rejects duplicate JSON keys and unsafe paths, and has explicit documented exclusions for build/QA/research-input directories, caches and container/checksum files. A manifest is an integrity inventory, not a signed authenticity certificate. These mutation tests establish detection of the tested faults; they do not claim detection of every possible implementation error.

The reproducible probe logs are `validation/auditor_probes_normal.log` and `validation/auditor_probes_optimized.log`. Run the probe script directly in either mode. Reproduction of the final archive and PDF is recorded separately by `replay.py`.

## Exact audited hashes

SHA-256 values for the unchanged finite checker, its four fixtures and the independent probe source:

| File | SHA-256 |
| --- | --- |
| `check.py` | `990f9f291e652e5dcf02cae4c82dc6675a966a95a4051891539c1582fb96d4ba` |
| `data/check_results.json` | `d1045728be9baf569fd37414063e62957f904a55266f1c1f9962b1617cd96c1c` |
| `data/coefficients.json` | `a43479f0ead60c5168b850ce15780f17b5b444d2467e3073d9a7b2426b57e12c` |
| `data/counts.json` | `90878e0159093b78023401c1e0835a85345880549f651e48b9a9d1e1b9145edd` |
| `data/height_counts.json` | `747b2d65f87e17c81f7dcf221f503932ecab327b21c92a9bf141fc3032e44214` |
| `validation/auditor_probes.py` | `fd6b88a48cf8e7a2cf5726aa1fe06ded79b1a8627e701b1387d7c6f1b8a1cbfb` |
