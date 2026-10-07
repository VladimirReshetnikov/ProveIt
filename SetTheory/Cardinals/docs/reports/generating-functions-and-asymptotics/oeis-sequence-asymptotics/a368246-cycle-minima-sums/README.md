# Report234: record sums and oscillatory asymptotics for A368246

This package contains the article, its source ledger, exact finite computations,
and a deterministic rebuild recipe. It is a research report, not a formal proof
assistant certificate or a publication-priority claim. See `SOURCES.md` for the
attribution boundary and the article for the analytic proof.

## What is proved, and what the code checks

For positive n, write b_n=a_n/(n-1)! for OEIS A368246. The article proves a
fixed-order expansion with leading constant exp(-EulerGamma), only nonconstant
root-of-unity frequencies in its algebraic corrections, and explicit terms
through n^-3. It proves a finite-model inverse error scale and a two-ceiling
integer envelope with unspecified constants and onset. It does not establish
convergence of an infinite transseries, uniform estimates as the order grows,
effective remainder constants, or an unconditional rounding rule.

`code/checks.py` prints a deterministic JSON receipt with 175 explicit checks:

- Integer counting-polynomial and independent rational infinite-product
  coefficients through n=60, including the exact shift m=n-1
- Independent enumeration of both record positions and cycle minima through n=8
- Exact rooted-tree cancellation through degree 40, and degree-40 root-filtered
  jets for root orders 2 through 14
- Symbolic local expansion, logarithmic coefficient transfer, parity and index
  shift, and the exceptional simple zero at the fourth roots
- 80-digit complex Gamma values checked against independent polylogarithm tails,
  with another computation at 110 digits
- Directed Decimal coefficient bounds checked against exact rational arithmetic
- K=2 and K=3 finite-model Newton roots, their analytic derivatives, and an
  independent secant evaluation

All guards use explicit conditions, not Python `assert`. The same receipt is
produced under normal and optimized Python. Numerical checks support the
calculation; they do not replace the analytic proof or discover higher actual
sequence coefficients from arbitrary formal fixtures.

## Requirements

The reference arithmetic toolchain is Python 3.12.14, mpmath 1.3.0, and SymPy 1.14.0.
The exact Python patch version is recorded in `code/receipt.json`. Install the
pinned Python dependencies in your usual environment using `requirements.txt`.
No program in this package accesses the network or installs software.

PDF rebuilding additionally requires `pdftex` and `pdflatex` on PATH and the TeX
packages used by `article.tex`. The reference engine is pdfTeX
3.141592653-2.6-1.40.26 (TeX Live 2025/dev/Debian). Byte-for-byte PDF reproduction
is toolchain-dependent; a different font or TeX release may produce a different
PDF and will be reported as a failure rather than silently accepted.

All examples below run from the package directory. Use `-B` to prohibit Python
bytecode files; strict manifest verification rejects unlisted cache files. All
child Python processes use `-B`; the integer-to-decimal digit cap is 640. Exact
sequence computation is bounded at n=200, all displayed integers fit under that
cap, and no unsafe global disabling of the cap is used.

## Read-only arithmetic checks

    python -B code/checks.py
    python -B -O code/checks.py
    python -B code/guard_tests.py
    python -B -O code/guard_tests.py

`code/receipt.json` is the frozen arithmetic certificate; `code/guard_receipt.json`
is the frozen guard-test receipt. The check programs write only to
stdout unless `--output` names a new file outside this package. An existing
output, an output inside the source package, live or dangling symlink ancestors,
and raw `.` or `..` path components are rejected. The parent directory must
already exist. Existing files are never merged or overwritten.

The guard suite tests 64 bounded-input, nonconvergence, exclusive-output,
symlink, path-component, malformed-manifest, and invalid-CLI cases in both optimization modes. These
are finite tests, not a general security proof.

## Reusable arithmetic CLI

    python -B code/record_sum.py exact --n 60
    python -B code/record_sum.py brute --n 8
    python -B code/record_sum.py roots --digits 80 --cutoff 115
    python -B code/record_sum.py inverse --log-y 1000 --order 2
    python -B code/record_sum.py inverse --log-y 1000 --order 3
    python -B code/record_sum.py decimal --n 1800 --digits 60

Each command accepts `--output /absolute/new/file.json`. Use `--help` on any
subcommand. The exact command computes the complete requested diagonal from
the finite counting polynomial and compares it to the independent Fraction
product; it does not read precomputed answers beyond the certificate's short
historical initial-value check.

The root evaluator isolates the j=1 factor before summing the polylogarithms.
At cutoff R the omitted logarithm is bounded in modulus by
3*2^(-R)/(R+1). The reported product-tail bounds follow by multiplying
expm1 of this quantity by the truncated product's modulus. These are analytic
truncation bounds. mpmath arithmetic is not interval-certified: the certificate
uses explicit tolerances and precision-stability checks for its roundoff.

The optional Decimal command encloses the exact finite coefficients using two
nonnegative products, with every division, multiplication and addition rounded
down and up, respectively. It allows 1 <= n <= 6000 and 20 <= digits <= 200.
These intervals cover Decimal roundoff in the finite products. They do not
bound the asymptotic remainder, special-function roundoff, or inverse thresholds.
Runtime is quadratic in n; larger diagnostic runs are optional and are not
needed for the default certificate.

### Finite Newton models

The inverse command uses exactly the real K=2 or K=3 interpolation displayed in
the article. In particular the self-conjugate (-1)^n frequency becomes cos(pi*x).
It solves log(Gamma(x))+log(B_K(x))=log(y), with

    L = log(y) + EulerGamma - log(2*pi)/2
    X = L / W_0(L/e)
    x_0 = X + 1

Here x_0 is an initial iterate. The article's Gamma-only displacement statement
is r_K=X+1/2+O(1/(X*log(X))), not r_K=X+1. The CLI accepts log(y) directly to
avoid constructing enormous targets. It requires 10 <= log(y) <= 10^12,
40 <= digits <= 200, and 1 <= max-steps <= 100 (default 30). Newton steps are
damped if necessary, with at most 60 halvings per step. A run succeeds only when
the absolute logarithmic model residual is at most 10^(-digits+15); otherwise
it fails explicitly. Iterates and the residual are included in the result. A separate
`finite_order_construction` output also evaluates exactly t_K=ceil(log2(K+2))
undamped steps from the same starter: two steps for K=2, three for K=3. This
finite construction fails explicitly if an iterate leaves the valid positive
model domain; it never substitutes damping for the prescribed iteration.

These are numerical roots of finite models. Their printed decimals are not
certified intervals. No effective asymptotic constant or onset is available;
the command does not label any rounded value as the sequence's integer inverse.

## Frozen source and PDF rebuild

`MANIFEST.sha256` lists every source-package file except itself, including the
frozen PDF and receipt. It detects changes, additions, missing files, unexpected
directories, and symlinks. A manifest is an integrity record, not a signature.

    python -B build.py --verify-only
    python -B build.py --output-dir /tmp/report234-build-new

The output directory must be new, outside the package, with an existing parent.
Raw dot components and all symlink ancestors are rejected. The build:

1. Verifies the frozen manifest and snapshots the source tree
2. Recomputes both arithmetic and guard checks and requires exact receipt equality
3. Compiles a disposable TeX source copy, with a private format/cache and
   `-no-shell-escape` on every TeX invocation
4. Rejects missing-character, overfull-box and unresolved-reference warnings
5. Requires the rebuilt PDF to match the frozen PDF byte for byte
6. Produces `Report234.pdf`, `Report234.zip`, `exact_checks.json`,
   `guard_checks.json`, and `build_checks.json` in the new output directory
7. Checks that the source tree has not changed

`logs/` contains the build logs. Their temporary paths are informational and
are not claimed to be byte-reproducible. PDF bytes, ZIP bytes, the arithmetic, guard-test
and build receipts are the reproducibility targets.

The ZIP stores every manifest-listed package file plus the manifest itself.
Members have sorted names under `Report234/`, stored compression, fixed
2026-10-05 timestamps and mode 100644. PDF dates use SOURCE_DATE_EPOCH=1791158400.
No TeX command is run in the source package and no system format cache is changed.

## Rebuild the actual ZIP twice

After the first build, independently extract and rebuild the actual delivered
archive under both normal and optimized Python:

    python -B code/reproduce_zip.py \
      --archive /tmp/report234-build-new/Report234.zip \
      --output-dir /tmp/report234-zip-rebuild-new

The verifier first requires all archive member bytes to equal this trusted
frozen package, so it does not execute arbitrary build code from an unrelated
ZIP. It validates names, duplicates, entry kinds and bounded uncompressed size,
then creates separate source trees and build outputs for the two modes. It
checks every rebuilt ZIP member and metadata, the full original/rebuilt ZIP
bytes, PDF bytes, all three receipts, and unchanged extracted sources. Results are
written to `reproduction_checks.json`; the original archive is also checked
unchanged. This verifies the actual packaged artifact, not merely two builds
from the author's working directory.
