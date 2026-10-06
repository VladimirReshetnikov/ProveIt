# Report236: Square tables, source and exact-computation package

This package accompanies the mathematical article `Report236.pdf`. Its
counting sequence is the number of labelled n by n nonnegative integer tables
whose row sums and column sums are all n. The empty table is counted once. The article also treats equal margins s
with density lambda=s/n in a fixed compact positive interval.
The PDF supplies the definitions, hypotheses, analytic arguments and references.
The programs supply reproducible finite algebra and small-size counting checks.
Computational agreement does not itself prove asymptotic remainder estimates,
localization, inversion error bounds or originality.

The executable coefficient computation has a deliberately fixed validated
range: diagram cost at most three, at most six vertices, degrees three through
eight, and total degree at most eighteen. These limits are not a statement that
the article's mathematical framework stops at this order. They prevent an
unbounded computation from being presented as a validated public feature.

## Files

- `article.tex`, `sections/`, `Report236.pdf`: article source and reference PDF
- `README.md`, `COMPUTATION.md`: use, algorithms, scope and reproducibility limits
- `SOURCES.md`: verified public-source links and attribution scope
- `requirements.txt`: pinned Python dependency versions
- `code/common.py`: finite input validation, exclusive output handling and artifact name
- `code/connected_wick.py`: exact connected-multigraph Laurent evaluator
- `code/formal_factorization.py`: independent complete-polynomial evaluator
- `code/small_gaussian.py`: independent scalar and three-Gaussian moment checks
- `code/inverse_reversion.py`: exact fixed-order symbolic inverse-series check
- `code/density_coefficients.py`: fixed symbolic geometric-density coefficient checks
- `code/verify_coefficients.py`: the independent checks combined
- `code/count_tables.py`: exact small-size table enumeration
- `code/diagnostics.py`: separately labelled floating-point diagnostics from a fixed OEIS fixture
- `code/guard_tests.py`: finite input, output, manifest and ZIP guard checks
- `code/*_receipt.json`: four deterministic expected receipts
- `build.py`: read-only verification and disposable-copy PDF rebuild
- `code/reproduce_zip.py`: actual-ZIP normal/optimized rebuild and comparison
- `MANIFEST.sha256`: hashes of every other packaged regular file

No program imports another report or any private working directory. No
third-party PDF or private review report is included. The executable checks,
build and ZIP replay use no network. The manifest is an integrity record, not a
digital signature or a proof of authorship.

## Requirements

The reference computational toolchain is Python 3.12, SymPy 1.14.0 and its
mpmath 1.3.0 dependency. The connected-graph evaluator, formal-factorization
arithmetic and table counter use only the Python standard library. SymPy is used
for an independent expansion of the geometric logarithm and for symbolic inverse
reversion. The density extension is checked through degree eight and diagram cost three as exact rational-function identities. The optional mpmath diagnostics use fixed 80-digit precision. No floating-point diagnostic is part of a mathematical receipt.

Install requirements in an environment of your choice:

    python -B -m pip install -r requirements.txt

PDF reproduction additionally needs `pdftex`, `pdflatex`, and the TeX packages
loaded by `article.tex`. A compatible TeX installation, fonts and package
versions are needed for byte-identical PDFs. A mismatch is reported; no program
silently updates the expected PDF or receipt to hide it. Build output records
the observed Python and pdfTeX versions.

## Run the exact checks

From the package directory:

    python -B build.py --verify-only
    python -B code/connected_wick.py
    python -B code/verify_coefficients.py
    python -B code/count_tables.py
    python -B code/guard_tests.py

These commands print JSON to standard output and do not rewrite the package.
The coefficient verifier checks all eighteen Laurent polynomials in the
coefficient receipt using a different algebraic construction, and checks each
again at n=1 and n=2 using direct Gaussian integration and the set-partition
cumulant formula. The resulting logarithmic coefficients are

    1/4 - 3/(2n) + 223/(32n^2).

The contribution to 223/32 from costs one and two is 35/8, and the cost-three
contribution is 83/32. No numerical fitting is used.

For formal density lambda and u=lambda*(1+lambda), the independent verifier also
checks the constant coefficient 1/3-1/(6u), first correction -3/2, and second
correction 1171/180+11/(12u)+1/(60u^2)+1/(180u^3), together with their density-one
reduction. An exact Stirling comparison also checks the coefficient
67/6+5/(3u) for the stated Canfield--McKay parameter. The analytic uniformity for lambda in compact positive intervals is
proved in the article, not by these finite symbolic computations.

The table counter verifies the exact prefix

    n = 0, 1, 2, 3, 4, 5
    a_n = 1, 1, 3, 55, 10147, 22069251.

A separate unsorted labelled recursion agrees through n=3. For a single count:

    python -B code/count_tables.py --n 5

To reproduce the six-place table of D1 and D2 in the article, separately run:

    python -B code/diagnostics.py

This uses a fixed fixture at n=4,5,6,8,10,13 and fixed 80-digit working precision.
The counts beyond n=5 come from the linked OEIS b-file; the public dynamic
program does not recompute them. The output is explicitly approximate and is
not part of the four exact/guard receipts or a finite-size error certificate.
The diagnostics also accept a new external `--output` file under the same path
rules. Their normal and optimized outputs agree on the pinned toolchain.

Only integer dimensions 0 through 5 are supported by the public table counter.
In Python, `connected_wick.cumulant(ds)` and
`formal_factorization.cumulant(ds)` accept degree tuples in the bounded domain.
The geometric-coefficient generator accepts maximum degrees 3 through 8.
Unsupported values, including booleans and inexact numeric values, are rejected.

All four check programs accept `--output /absolute/new/path.json`. The parent
directory must already exist and the output file must be new and outside the
package. Source-tree outputs, existing files, symlinks or symlink ancestors,
dot/dot-dot traversal and backslash components are rejected. Final output
creation is exclusive. This is ordinary defensive filesystem handling, not a
sandbox against hostile concurrent path replacement.

Every public safeguard uses explicit exceptions and remains active under `-O`:

    python -B -O code/connected_wick.py
    python -B -O code/verify_coefficients.py
    python -B -O code/count_tables.py
    python -B -O code/guard_tests.py

The 640-digit Python integer-to-decimal conversion cap is retained throughout.
All Python subprocesses are launched with `-B`; no bytecode files should appear
in the input source tree. Use the shown `-B` option for direct invocations too.

## Rebuild the reference package

Choose a new output directory with an existing parent:

    python -B build.py --output-dir /tmp/report236-build

The build verifies the full manifest; rejects extra, missing, symlink or
nonregular source entries; creates a fresh external output directory; reruns
all four receipts; and requires exact byte agreement with the reference
receipts. It then creates a private TeX format and compiles a disposable copy of
the article three times with shell escape disabled. It rejects the listed
unresolved-reference, missing-character and overfull-box warnings and requires
the resulting PDF to equal the reference PDF byte for byte.

Outputs are `Report236.pdf`, `Report236.zip`, four JSON receipts, logs
and `build_checks.json`. The package tree is checked for changes after the build
and after archive assembly. The build cannot refresh the source receipts or PDF.

ZIP members are sorted, stored without compression, assigned the timestamp
2026-10-05 00:00:00 and Unix regular-file mode 0644. TeX receives
`SOURCE_DATE_EPOCH=1791158400`, UTC and a fixed locale. TeX auxiliaries, the private
format and its caches remain in a disposable working directory. No compiler
artifact is written to the source package.

The artifact stem is defined once as `ARTIFACT_STEM` in
`code/common.py`. Renaming a release requires an editorial source change,
matching PDF/documentation filenames and a new manifest. The public rebuild
never performs that change itself.

## Replay an actual ZIP

After producing the archive:

    python -B code/reproduce_zip.py --archive /tmp/report236-build/Report236.zip --output-dir /tmp/report236-replay

The replay validates ZIP paths, types, sizes and counts. Before executing any
extracted code, it requires every archive member's bytes to match this trusted
source package exactly. It then makes two independent extractions, rebuilding
one under ordinary Python and one under `-O`.

Both rebuilt archives must match the input archive member by member, including
metadata, and as complete ZIP byte streams. Both PDFs, all four receipts and
build-check outputs must be identical. The input ZIP, the trusted source and
both extracted sources must remain unchanged. The external
`reproduction_checks.json` records the results and hashes. This is a replay of
the actual archive, not just a directory hash or selected-file comparison.

## Limits of the checks

The connected evaluator and formal-factorization verifier agree as exact finite
Laurent identities, rather than by interpolation at a few n values. Their
shared fixed specification list and exact covariance identify what is being
checked; their graph generation and moment constructions are separate.
The n=1,2 checks provide a third finite route, not a proof of a polynomial
identity by sampling.

The inverse checker cancels four coefficients in a fixed formal expansion of
F2(x)-log(Y). It does not turn a truncated logarithmic formula into an exact
finite-n identity, and does not numerically bracket roots. The article must
justify all analytic remainder estimates and the step from real inversion to
any statement about the integer sequence. See `COMPUTATION.md` for the precise
formal calculation.
