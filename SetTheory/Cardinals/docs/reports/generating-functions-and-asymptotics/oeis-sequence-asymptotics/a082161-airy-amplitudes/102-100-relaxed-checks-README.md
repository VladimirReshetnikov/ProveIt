# Reproducible finite exact verification

This package checks the finite algebra and formal coefficient certificates accompanying the relaxed-tree report. It does **not** establish amplitude convergence or asymptotic transfer; those require the report's analytic arguments and their audit. Compacted-tree calculations here certify only the indicated formal dominant-series identities. No exponentially small sector is claimed.

## Replay

Use Python 3.12 and SymPy 1.14.0 (the recorded environment); no NumPy, SciPy, mpmath numerical evaluation, network, or other research directory is needed. SymPy's normal dependencies are sufficient. From this directory:

```
python verify.py
python -O verify.py
python negative_tests.py
python -O negative_tests.py
```

The default command runs the complete exact suite, including fresh triangular and generic linear solves. Every acceptance gate uses an explicit exception; no Python `assert` statement is used. `-O` therefore retains the tests. The corruption suite deliberately causes rejection and treats an incorrectly accepted corruption, wrong failure reason, reduced coverage, or missing case as an error.

For a quick integrity/algebra check, use `python verify.py --mode algebra`. Partial modes `integrity`, `schema`, `algebra`, and `formal` explicitly report their limited scope. The full certificate is the default `full` mode. Optional bounds are deliberately fixed: `--max-n 30 --formal-order 9`. Other bounds, malformed types, unsupported modes, unknown options, and empty/missing coefficient tables fail closed. There is no `--skip-integrity` switch.

## Exact coverage

- Original relaxed integer recurrence and every parity-allowed weighted-meander state at times 1 through 60: 960 normalized rational state comparisons, using triangle rows through 60; the relaxed diagonal relation through n=30
- The two one-step transitions versus the two-step operator at every n=1 through 30, both on the actual vector and on every basis input: 9,920 matrix entries
- All 495 states at n=1 through 30: positive symmetrizer squares, exact diagonal similarity on edges, positive Jacobi off-diagonals, the bidiagonal Gram-factor identities, zero off-band support, and the R-square formula/contraction including n=1 and zero-extension endpoints
- The Gram check verifies diagonal equality and positive edge squares; positive square roots determine the corresponding entries uniquely, so this is an exact factorization check, not a floating eigenvalue test
- Both R and C coefficient datasets must contain exactly profiles f_0 through f_7 as length-two polynomial pairs and sigma_0 through sigma_9, with fixed normalization and exact rational-polynomial domains
- All 40 polynomial-pair recurrence coefficients (two components, ten powers, two sequences), every ghost boundary, and every derivative gauge
- Fourteen fresh construction stages: the explicit triangular inverse agrees with a generic exact linear-system solve at each stage 3 through 9 for each sequence; generated coefficients also agree with both archived datasets (104 component/scalar comparisons). These two solvers share the polynomial-pair shift arithmetic, so the comparison is independent linear algebra, not a wholly independent implementation of the recurrence
- Discrete formal integration of log(s/2), endpoint Taylor evaluation, log corrections 1 through 6, multiplicative coefficients 0 through 6, and ratio coefficients 0 through 9, including an independent ratio-from-integrated-log conversion: 66 endpoint coefficient comparisons

The finite coverage counts are explicit acceptance gates. Data must have exact keys, exact lengths, exact polynomial string types, no duplicate JSON keys, no unexpected files in `data/`, and no unsafe expression syntax. JSON expressions are parsed using a restricted AST arithmetic grammar, not evaluated with `eval` or unrestricted `sympify`.

## Integrity and provenance

`manifest.json` contains an exact expected inventory with byte lengths and SHA-256 hashes for every executable source, coefficient table, package README, requirements, provenance record, and archived diagnostic. The verifier checks that inventory, hashes, lengths, hash syntax, and absence of file/parent symlinks. The manifest is an integrity record, not a digital signature or independent proof of the code's correctness; protect the enclosing archive/checksum when transporting it. Logs and Python bytecode caches are runtime output and are excluded from this source manifest.

`provenance/source_hashes.json` records hashes of the research inputs inspected while preparing these checks, with the original roles and explicit archival distinctions. The hardened implementation was derived from those sources and expanded to remove optimized-away gates, reject missing coverage, freshly compare solvers, and certify every endpoint coefficient family. Original research files are not required at replay time and are not modified. No external authors' PDF or Maple sources are bundled.

`logs/` records normal and optimized complete runs and both negative suites, together with environment/command records. Exact finite equality outcomes should be the same across compatible SymPy versions, but the pinned version is recommended for reproduction. Runtime durations are environment-dependent.

## Deliberate-error regressions

The negative suite requires exactly 53 expected rejections and checks active exception gates, bounds/type failures, empty/missing/extra dataset keys and indices, invalid polynomial forms, duplicate/nonfinite JSON, normalization errors, byte-length and same-length hash corruption, malformed/incomplete/extra manifest entries, extra data files and executable sources, a deliberately corrupted two-step coefficient after re-hashing a temporary local copy, a boundary-preserving formal coefficient edit, all three endpoint coefficient families, and thirteen CLI rejection cases. It runs in a private temporary directory and never modifies the accepted package.

## Numerical/analytic boundary

`diagnostics/exact_dp_3000.json` is retained under its original filename for traceability, but contains **archived high-precision diagnostics**, not stored exact integers or certified intervals. Those numerical estimates are not checked against the exact-count recurrence here, and no amplitude digits are certified. See `diagnostics/README.md`. The expensive n=3000 run is intentionally not repeated.

A successful run corroborates exactly the finite identities and coefficient certificates listed above. It does not turn finite experiments into a proof of infinitely many identities, a positive limiting amplitude, arbitrary-order remainder bounds, compacted asymptotics, or numerical precision claims.
