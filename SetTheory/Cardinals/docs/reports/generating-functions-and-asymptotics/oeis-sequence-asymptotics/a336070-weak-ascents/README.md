# Report 105 — Weak ascent sequences and fixed difference ascent growth

Prepared for Vladimir, 2 October 2026.

## Main result

For A336070, with mu = 6/pi^2,

log(a_n/(n! mu^n)) = (1/2)(log n)^2 + O((log n)^2/log log n).

The report proves the factorial-normalized root limit, scaled consecutive-ratio limit, and exponential concentration of the ascent count at mu. Those three conclusions also hold for each fixed nonnegative integer difference-ascent parameter d, with the convention x_(i+1) > x_i - d. The sharp logarithmic-square correction is proved only for d=1.

For L=log X and x=L/W(mu L/e), the integer threshold satisfies

N(X) = x - (log x)^2/(2 log(mu x)) + O(log x/log log x).

The report includes detailed proofs, exact recurrences, formal generating-function interpretations, source references, numerical diagnostics, and remaining questions. This is substantial partial asymptotic progress. It is not a relative-error coefficient equivalent, amplitude formula, full tilted-pressure theorem, central limit theorem, or transseries.

## Files

- `report105.pdf`: sealed 24-page report, also delivered separately
- `report105.tex`: complete standalone LaTeX source
- `build.sh`: reproducible three-pass PDF build and fail-closed TeX warning checks
- `data/weak_ascent_terms.txt`: exact integer terms n=0,...,500, generated from the positive recurrence
- `data/exact_certificate.json`: complete finite rational/integer certificate
- `code/verify_exact.py`: exact verifier, using Python's standard library
- `code/exact_models.py`: certificate formulas and independent finite models
- `code/build_certificate.py`: regenerate the certificate
- `code/run_checks.py`: normal/optimized exact checks and deliberate-corruption tests
- `code/exact_check_results.json`: recorded exact test results
- `code/sanity_moving_bounds.py`: optional, separate mpmath numerical sanity checks
- `code/floating_sanity_results.json`: recorded floating-point results and table diagnostics
- `PROVENANCE.json`: public sources, data provenance, and scope
- `VALIDATION.json`: PDF/source hashes and validation scope
- `MANIFEST.sha256`: checksums of all archive payload files except the manifest itself

The sealed PDF is included in this archive and delivered separately. It can be regenerated from the included source. The archive contains no private research notes, source-paper PDFs, build caches, page images, or repository files.

## Replay from a fresh extraction

From the extracted `report105_source` directory:

```sh
sha256sum -c MANIFEST.sha256
python3 code/run_checks.py
bash build.sh
```

The exact runner performs complete checks both normally and with `python3 -O`, then tests seven deliberate-corruption categories in each mode. It rejects malformed JSON, missing or extra cases, altered rational claims, duplicate JSON keys, wrong JSON types, and a modified final stored term. All mathematical arithmetic in this suite is integer or rational; no approximate tolerance is used. Python `assert` statements are forbidden and checked syntactically, so optimization cannot silently disable validation.

The exact suite regenerates every stored count through n=500, compares all derivative-recurrence polynomials through degree/length 16, checks the original uncancelled catalytic equation, independently enumerates all inversion sequences through length 7 for d=0,1,2,5, and verifies finite rational Perron, band-comparison, Poisson, stationary-moment, wrap-loss, and state-tracking identities. Full inventories and counts are in the JSON results.

The optional floating-point suite requires mpmath (tested with 1.3.0):

```sh
python3 code/sanity_moving_bounds.py
```

It is deliberately separate from the exact checker. Its finite high-precision samples are sanity checks, not exact rational certificates or proofs of all-n estimates.

To save a new run without changing the archived recorded results:

```sh
python3 code/run_checks.py --output /tmp/report105-exact-replay.json
python3 code/sanity_moving_bounds.py --output /tmp/report105-floating-replay.json
```

## Requirements and interpretation

The exact suite needs Python 3.9 or later and only its standard library. A full run executes both ordinary and optimized checks and may take around a minute, depending on the machine. The PDF build needs pdfTeX/LaTeX with the packages listed in the source, including Latin Modern, amsmath, amsthm, microtype, geometry, booktabs, enumitem, fancyhdr, and hyperref. The build creates a local TeX format when required; it does not download or install software. Reproducible PDF bytes are expected when the same TeX toolchain and fonts are used; different TeX versions may produce visually equivalent but byte-different output.

All 24 rendered PDF pages were visually checked. The finite computations detect input, algebra, and implementation errors; they do not establish asymptotic theorems. Those theorems are justified by the proofs in the report, using the cited ordinary Fishburn asymptotic as the external asymptotic input. The unspecified asymptotic error constants are not certified finite numerical bounds. For a particular finite threshold X, use the exact recurrence and integer comparisons.
