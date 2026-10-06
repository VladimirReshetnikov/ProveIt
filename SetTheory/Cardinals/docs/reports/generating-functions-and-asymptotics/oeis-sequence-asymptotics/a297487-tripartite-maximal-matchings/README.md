# Report176: Maximal matchings in balanced complete tripartite graphs

This package accompanies the report on OEIS A297487. It contains the manuscript,
exact rational/integer certificates, a standard-library Python verifier, and an
offline deterministic PDF/ZIP build. The report derives and refines the credited
leading asymptotic; no global-priority claim is made.

## Read and verify

Requirements: Python 3.10 or later. The exact verifier has no third-party Python
dependencies and needs no network access.

```sh
python -B verify.py
python -O -B verify.py
python -B guard_tests.py
python -B regenerate.py --compare data/certificates.json
```

The verifier checks every retained coefficient through order five, the four
printed elementary/logarithmic corrections, directly inserted first/second
moments, the odd fixed-shift ratio through four powers of `1/lambda^2`, both
rare-maximum probability corrections, exact counts for `0 <= n <= 100`, a
separate labeled-matching recursion for `0 <= n <= 8`, and all 16 source-displayed
OEIS values, and compares the manuscript’s nine displayed initial values with
the exact certificate. It also checks the two inverse-refinement coefficients and 48
finite rational ceiling-boundary cases. The included numerical reference was produced by a separate
symbolic audit and is read without executing code. See `README_CODE.md` for
conventions, algorithms and limitations.

## Build the report

An installed TeX stack with `pdflatex` and `kpsewhich` is required. This package
never downloads or installs dependencies. From the extracted package, choose a
new output directory whose parent exists:

```sh
python -B build.py --output /absolute/path/to/new-output
```

The builder runs the verifier and corruption/build guards under normal Python
and `python -O`, then compiles with shell escape disabled. All calculations,
auxiliary TeX files and caches are isolated in temporary storage. Existing
outputs are refused. The resulting directory contains `Report176.pdf`,
`Report176.tex`, `Report176.zip`, and `ARTIFACTS.json` with their SHA-256 digests.

The ZIP contains the exact source inventory, generated verification receipts,
and `SHA256SUMS.json`. Extract it into a fresh empty directory, then run:

```sh
python -B verify_manifest.py
python -B build.py --output /absolute/path/to/another-new-output
```

With identical sources and the same installed Python/TeX stack, the PDF, TeX and
ZIP artifacts are byte-identical. Cross-version TeX/Python identity is not
promised. Running the supplied commands with `-B` avoids bytecode caches; the
manifest deliberately rejects all extra files, including caches.

## Scope

Exact arithmetic certifies the algebraic identities and finite combinatorial
checks, not the analytic remainder bounds. The mathematical arguments are in
the report. No effective asymptotic onset, exponentially accurate counting
transseries, or universal literature nonoverlap is certified by these scripts.
The source b-file was unavailable during the source check: only the 16 displayed
OEIS values are claimed as source comparisons. The other 85 counts are exact
computations, not a claim of external-source verification.
