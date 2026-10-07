# Code provenance

All included mathematical code is authored for the A239950 investigation and this report. No downloaded third-party executable code is included or executed by the mandatory workflow.

The positive DP is a cleaned functional version of the investigation's authored `count_exact.py`. The independent small-partition enumerator, exact Euler transform, and rational disk-zero certificate originate in its authored `verify_exact.py` and `certify_nonproduct.py`. The optional Wick program is adapted from the independent derivation's authored `independent_wick_check.py`; its two assertions were replaced by unconditional exception checks and numerical diagnostics were removed.

The optional second-correction verifier is adapted from the authored direct derivative/Wick calculation for this sequence. Assertions were replaced with unconditional exceptions, timing and floating diagnostics were removed, and full identities against the explicit B2 polynomial and d2/c2 formulas were added. The coordinate change is documented in the public source. This is an algebraic check of finite coefficients under the report's analytic theorem, not an independent proof of transfer.

The generic bounded-file, symlink-refusal, manifest-schema, isolated-TeX-environment, installed-format fallback, and deterministic-ZIP patterns are adapted from the authored Report194 release toolchain. No matrix combinatorics, matrix certificates, unrelated data, or unrelated tests are included. `test_build.py` is tailored to this report's sources, positive partition DP, rational certificates, release inventory, extraction, and replay.

This is provenance disclosure, not an external code-authentication claim. Release manifests detect changed bytes against the included manifest; an attacker who replaces both the payload and manifest is outside that guarantee. The package is a reproducible research artifact, not a security sandbox for untrusted Python or TeX source.
