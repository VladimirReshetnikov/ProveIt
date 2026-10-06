# Report223 Strict partition chains and their asymptotic expansions

A self-contained mathematical article on OEIS A005121, with exact code and a
reproducible PDF and source archive. The objects are arbitrary strict chains
from the discrete partition to the one-block partition. H counts strict
transitions, so H_1 = 0. The PDF is `Report223.pdf`; editable source is
`Report223.tex`.

## Mathematical scope

The article proves a rigorous expansion at every fixed inverse-power order on
the known factorial-square scale, using elementary factorial domination, a
uniform block-defect/Cauchy remainder, and first-difference contraction. It
constructs all correction polynomials and displays c_1 through c_4. A single
complex contraction disk |q-1| <= 1/16 works for every fixed order, with one
further shrink for a nonzero analytic limiting constant. The marked theorem
gives every fixed cumulant expansion and explicit mean/variance corrections.
It also specializes Lambert-W inversion, eventual sampled-value recovery,
and arbitrary-threshold two-ceiling enclosures with an error interval of
width less than one before claiming adjacent candidates.

The leading equivalent, positive constant, leading mean and CLT are prior
results. Prellberg announced formal higher corrections. The full unfinished
Flajolet-Salvy 1990 manuscript was not recovered. Related ProveIt
proportional-depth iterated-Bell results are credited after comparison of the
actual pinned article. Neither first coefficients, a general open-problem
resolution, nor new generic inversion theory is claimed. The source boundary
and direct links are in the article and `SOURCES.json`.

Every asymptotic order is fixed. No convergence/Gevrey/late-order theorem,
local limit, Edgeworth expansion, large deviations, evaluated inverse cutoff,
or interval-certified constant is claimed. The formal exponential generating
function has radius zero. The pinned OEIS revision #79 (30 May 2026) contains
a minus-sign inconsistency: the exact recurrence gives
2 Z(z) = z + Z(exp(z)-1). No external source was modified.

## Package inventory

Source files:
- `Report223.tex`: complete article and bibliography
- `README.md`: this guide
- `SOURCES.json`: source URLs, inspected scope and full SHA-256 fingerprints
- `requirements-optional.txt`: optional symbolic/numerical dependencies
- `build.py`: offline full rebuild and exact inventory/checksum verification
- `code/lengyel_exact.py`: standard-library exact core and CLI
- `code/test_lengyel_exact.py`: independent exact checks and real CLI tests
- `code/symbolic.py`: optional exact coefficient and inverse algebra
- `code/diagnostics.py`: optional local-context numerical consistency checks

Regenerated files:
- `Report223.pdf`
- `generated/exact_checks.txt`
- `generated/symbolic.txt`
- `generated/diagnostics.txt`
- `generated/toolchain.json`
- `SHA256SUMS`: all other package members, including their full SHA-256 hashes

The archive has exactly these 15 files. The archive is outside the package
and cannot hash itself. Its full SHA-256 and the PDF's SHA-256 are recorded in
`ARTIFACT_SHA256SUMS` beside the archive after rebuilding. Source PDFs,
third-party repository files, private research notes, and TeX/cache files
are not redistributed.

## Exact core

Python 3.11 or newer, standard library only:

    python -B code/lengyel_exact.py value 200
    python -B code/lengyel_exact.py sequence 6
    python -B code/lengyel_exact.py polynomial 6
    python -B code/lengyel_exact.py moments 6 4
    python -B code/lengyel_exact.py inverse 9013 --max-n 20

The last command prints 7: z_6 = 9012 < 9013 <= z_7 = 262760.
The inverse takes a positive integer threshold T and returns
min{n >= 2 : z_n >= T}, only if it is attained within the given bound.
A failure means the finite search budget did not reach T, not that an inverse
does not exist. This exact inverse does not use C or asymptotic rounding.

The API provides `stirling_row`, `chain_numbers`, `chain_value`,
`chain_polynomial`, `raw_moment_totals`, `raw_moments`, `cumulants`,
`threshold_inverse`, `integer_to_decimal`, and `rational_to_decimal`.
Polynomial tuples have increasing powers of q. Raw moments include order zero
(one); cumulants include an index-zero placeholder (zero).

Deliberate resource limits:
- Values, sequences, Stirling rows and bounded inverses: n <= 1000
- Chain-length polynomial: n <= 150
- Moments and cumulants: n <= 600, order <= 12
- Positive inverse target: at most 6000 ASCII decimal digits
- Optional symbolic generator: orders 1 through 4 (default 4)

These are implementation bounds, not mathematical limitations. Inputs are
validated for type, syntax, size and budget; signs, separators, leading zeroes
and non-ASCII digits are rejected in CLI numeric fields. Trusted computed
integers and rational numerators/denominators are printed in <=600-digit
chunks. The programs never change the process-wide integer conversion limit
or recursion limit. The numerical script uses a cloned mpmath context rather
than changing global precision.

## Exact tests and optional calculations

    python -B code/test_lengyel_exact.py
    python -B -O code/test_lengyel_exact.py
    PYTHONINTMAXSTRDIGITS=640 python -B -O code/test_lengyel_exact.py

The explicit checks remain enabled under -O. They enumerate every partition,
comparable pair, and strict endpoint chain for n <= 6; compare inclusion-
exclusion Stirling counts; verify factorial domination for all 5050 pairs
through n=100; check exact polynomial, derivative, raw-moment and cumulant
implementations independently; and verify inverse minimality and guard
behavior. Real cap640 subprocesses output z_200 (719 digits), read a large
threshold, and print rational moments/cumulants with pieces exceeding 640
digits. Those outputs are independently parsed in nine-digit chunks. Merely
setting the cap on small examples would not test the advertised behavior.

With SymPy and mpmath installed:

    python -B code/symbolic.py
    python -B code/symbolic.py --order 3
    python -B code/diagnostics.py

The symbolic script derives rather than just substitutes the correction
coefficients; it independently checks the kernel using exact Stirling-diagonal
interpolation and checks polynomial degree, Touchard identities,
triangular multipliers, logarithmic coefficients, mean/variance corrections,
and formal inverse cancellation through order four. The arbitrary-fixed-order
mathematical construction is proved in the article; the script's bounded
implementation is not a growing-order theorem.

`generated/diagnostics.txt` is explicitly non-certified. It recomputes exact
integer moment totals before evaluating finite-n corrected normalizations and
centered mean/variance quantities at 80 decimal working digits. It also tests
the inverse model with a free K=7, not a supposedly certified Lengyel constant.
The printed C, K_1, and K_2 estimates are not intervals and must not be used as
certified threshold decisions.

## Full offline rebuild

A full rebuild additionally needs SymPy, mpmath, and an installed pdfTeX/LaTeX
with the article's packages (amsmath, amssymb, amsthm, mathtools, lmodern,
geometry, microtype, hyperref, enumitem, booktabs and their dependencies).
The exact dependency versions and pdfTeX banner used for the release are
recorded in `generated/toolchain.json`. `requirements-optional.txt` pins the
Python libraries. No network access or downloaded program is used by a build.

From a freshly extracted ZIP, first verify all actual members:

    python -B build.py --verify-only

Then choose a new sibling output directory; it must not already exist:

    python -B build.py --output ../rebuilt-normal

This regenerates every generated member, compiles until TeX references
stabilize, checks for overfull boxes and unresolved references, creates a new
complete `package/`, and writes `Report223.zip` plus `ARTIFACT_SHA256SUMS`.
It initializes a private TeX format/font-map environment using the installed
TeX distribution if needed, rather than writing to the user's TeX cache.
The source/extracted package is never modified. Use `-B` to avoid local Python
bytecode files, which deliberately count as unexpected package members.

To compare normal and optimized supported-cap full rebuilds, extract the
original archive again into a separate fresh directory and run:

    PYTHONINTMAXSTRDIGITS=640 python -B -O build.py --output ../rebuilt-optimized

Both output archives should be byte-identical to the original under the
recorded toolchain. Compare the whole archives, not just selected outputs:

    cmp Report223.zip rebuilt-normal/Report223.zip
    cmp Report223.zip rebuilt-optimized/Report223.zip

Run these two comparisons from the parent directory that contains the original
archive and those output directories, adjusting only the relative paths to
match your chosen layout. SHA256SUMS inside each package verifies every member.
The final artifact checksum file verifies the whole archive and the PDF.

The PDF suppresses dates and the trailer identifier. The archive uses sorted
member names, fixed 1980-01-01 timestamps, fixed regular-file permissions, and
ZIP_STORED (no zlib-version-dependent compression). The source and generated
text do not contain run dates or temporary absolute paths. Optimized execution
and the cap640 environment do not change actual member bytes or archive bytes.
Byte identity across different TeX/font/Python-library versions is not
promised; reproduce the recorded toolchain for archival byte comparison.

## Interpretation and provenance

The mathematical proofs are in the article, not in decimal agreement or a
finite test suite. Tests guard implementation and indexing. In `SOURCES.json`,
`sha256` fingerprints the raw file bytes at the source URL. For the two pinned
ProveIt records, separately named `retrieved_text_sha256` fields retain the
hashes of the inspected connector-returned UTF-8 texts, each of which has
exactly one extra terminal LF byte. Removing just that byte reproduces the raw
SHA-256 and stated Git blob identity; both byte counts and representations are
recorded explicitly. The original inspected-text provenance is preserved.
Source fingerprints do not license redistribution. The public package includes
links and bibliographic scope, not those sources.
