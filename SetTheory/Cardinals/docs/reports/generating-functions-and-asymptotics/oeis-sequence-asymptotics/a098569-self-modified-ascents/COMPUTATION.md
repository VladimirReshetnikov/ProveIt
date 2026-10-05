# Computational supplement to Report242

## Proof and computation have different roles

The article proves the asymptotic expansions, tail estimates, limit laws, and
inverse brackets analytically. The programs perform bounded exact checks,
noncertified high-precision numerical diagnostics, and byte-reproducible
packaging. They do not establish asymptotic remainder constants, a usable
finite threshold for any big-O statement, an interval certificate, or an
unconditional exact-ceiling inverse. No coefficient is fitted to numerical data.
Operational input cutoffs are not hypotheses of the mathematical theorems.

## Exact enumeration and size indexing

`code/exact_counts.py` evaluates both finite binomial sums, with b_0=c_0=1.
The historical conventions are checked against the source-linked fixture
`code/source_prefixes.json`: 26 terms of A098569 and 25 terms of A121690,
starting at OEIS index zero and matrix total size one. Thus b_N=A098569(N-1)
and c_N=A121690(N-1) for N>=1. The triangle convention is
A098568(n,k)=T(n+1,k+1); its zero-based column corresponds to dimension k+1.

An independent computation multiplies the individual cell generating
polynomials. For ordinary matrices it multiplies M copies of
1+x+x^2+... after reserving one unit for each diagonal entry; for binary
matrices it multiplies L copies of 1+x. Coefficient arrays are truncated at
the requested total-size bound. This route uses additions rather than the
closed binomial formula.

The default exact check covers N=0..40. It checks 82 complete polynomial rows
(two models at 41 sizes), 820 positive-size triangle entries, 820 conditional
binary products, 820 fixed-dimension binomial-transform identities, 1,640
residual-cell tail identities, and 40 total binomial transforms. The exact
conditional product is checked even at infeasible binary dimensions, where
one factor is zero. Empty objects, the triangle origin, and the first binary
infeasibility are also tested. An additional independent cell-polynomial dynamic program carries the total
count and the summed diagonal/off-diagonal violation indicators while
adding cells. Its coefficients count a diagonal indicator at residual at
least one, and an off-diagonal indicator at residual at least two. At all
820 positive-size (N,m) pairs it agrees with the exact total count and both
conditional first-moment formulas, giving 1,640 expectation comparisons.
The diagonal expectation is explicitly zero at q=0; the off-diagonal
expectation is zero at q<2. The corresponding rational formulas are
evaluated only when their denominators are nonzero. The empty object has
zero violations of both kinds.

Finite ordinary strict monotonicity after size
one and binary weak monotonicity are checked; these checks do not replace
the article's monotonicity proofs.

Exact sums are also computed at N=100,200,500,1000,2000. Their receipt contains
bit lengths and SHA-256 hashes of minimal nonempty unsigned big-endian byte
encodings. Zero is encoded as one zero byte. A decimal count is included only
when its bit length is at most 512. Large counts are never converted to
large decimal strings, and no decimal conversion limit is disabled.

## Gaussian, moment, ratio, and inverse algebra

`code/algebra_checks.py` independently enumerates finite weighted
multiindices. Ordinary variables lambda_j have weight j-2, while binary
penalty variables eta_j have weight j. Each monomial receives its exact
Gaussian moment and rational factorial coefficient. The explicit formulas
for C_1 and C_2 and the quotient coefficients Q_1 and Q_2 are compared with
these generated expressions. C_3 is also generated and used in diagnostics.
There are 2, 5, and 11 ordinary contraction terms at orders one, two, and
three; the binary numerator has 5 and 20 terms at orders one and two.

A second route expands the exponential by weight through four, then takes
Gaussian moments, and checks the same numerator polynomials. Further exact
symbolic checks establish the standardized mean and second-moment
corrections, the variance correction after subtracting the mean square,
the leading constants 1/24 and 1/1152, the explicit rational R(u) probability
correction, the identity F_0'(N)=u, the inverse v-equation, and the elementary
ordinary/binary inverse-seed separation v/2+1. These are finite algebraic
identities; differentiable remainder estimates are supplied by the proof.

## Bounded noncertified numerical diagnostics

`code/saddle_diagnostics.py` uses mpmath with 90 decimal digits and displays
30 significant digits. The default cases are N=100,200,500,1000,2000 with
mark t=0, together with (N,t)=(500,-0.25),(500,0.25). All sums use exact
integer weights before any marked weighting or floating conversion.

The exact gamma phase is retained. A finite-precision bisection solves each
saddle equation, checking opposite endpoint signs and the computed residual,
with at most 300 steps. Derivatives through order eight are evaluated by
mpmath differentiation. The script records C_1,C_2,C_3; unscaled relative
residuals through these corrections; corrected mean and variance errors;
the mass outside the stated dominant interval; and the leading local-limit
error over every support point. The inverse diagnostic also evaluates the
phase at nearby noninteger total sizes.

Unmarked cases additionally record the exact binary probability, the binary
saddle and its predicted shift, Q_1 and Q_2, the exact-h probability residuals,
the implicit-u correction, both signs of the elementary count carrier, and
both elementary inverse seeds at exact count thresholds. The central
integer-dimension gamma ratio is compared with its exact rational count.

At X=b_1000 the ordinary elementary inverse seed is
1000.00141646053388660135456785, whose ceiling is 1001, although the exact
threshold is 1000. This is an explicit regression check against treating an
asymptotic seed as an exact rounding rule. A separate sign-bracketed secant
calculation, limited to 20 steps, inverts the K=2 smooth exact-gamma carrier
at the same threshold. Its estimated root is
1000.0000000001411652229062555, with a finite-precision log residual about
-1.20e-44. Even an accurate smooth carrier can lie on the wrong side of an
integer threshold. Neither floating sign checks nor these residuals are
interval-certified, and no unknown asymptotic error constant is estimated
from them.

## Finite API and command-line domains

- Exact rows and total counts: integer N=0..2000
- Triangle indices: n=0..1999 and k=0..n
- Independent cell-polynomial rows and violation-moment rows: N=0..40
- Exact-count verification: maximum N=26..40
- Ordinary contractions: order 0..3; binary contractions: order 0..2
- Gaussian moment degree: 0..32
- Saddle cases and diagnostic maximum: integer N=100..2000
- Marks: exactly the strings `0`, `-0.25`, and `0.25`
- Exact integer byte records: nonnegative integers no greater than 2^40000

Boolean values are rejected where an integer is required; binary flags must
be actual booleans. Public computational entry points validate their domains
before expensive work. Private helpers are used only with validated,
fixed-size internal data. Each script internally sets the integer decimal
conversion cap to 640 and disables bytecode writes. Every documented Python
invocation and every Python subprocess command explicitly supplies `-B` and
`-X int_max_str_digits=640`; child environments also repeat the cap and clear
ambient optimization. No assertion implements validation, so guards remain
active under Python `-O`.

## Immutable build and actual-ZIP replay

`build.py` first verifies the complete manifest: hashes, member names, and
all implied directories. Unexpected files, empty extra directories, symlinks,
special entries, malformed or duplicate manifest entries, and files outside
the public allowlist are rejected. The source inventory is limited to 500
files, 1,000 entries, and 32 MiB, and the manifest to 128 KiB. The manifest
is never regenerated by the builder.

Outputs require a new directory outside the sources. Existing destinations,
dot or dot-dot components, backslashes, missing parents, and live or dangling
symlink ancestors are rejected. Created files use exclusive creation. These
are bounded regression and filesystem checks, not a general security proof
or a defense against hostile concurrent filesystem mutation.

Four freshly computed receipts must match the frozen receipts exactly.
The builder compiles a disposable copy of the TeX sources inside the checked
external logs directory, with a private format and cache, restrictive file
access, shell escape disabled, and three document passes. It rejects missing
glyphs, undefined references, and overfull boxes. The PDF must equal the
included frozen PDF byte for byte. Source inventories are compared before
and after compilation, the full build, and archive assembly. No build output
is written to a source tree.

SOURCE_DATE_EPOCH is 1791158400 (5 October 2026, UTC); locale and timezone are
fixed. The ZIP uses a single `Report242/` prefix, sorted stored members,
5 October 2026 00:00:00 timestamps, and Unix regular-file mode 100644. It
includes the source files, PDF, four receipts, and manifest, but not build
logs or itself. Build children have 180-second timeouts; archive replay
allows 900 seconds per complete builder; guard probes allow 30 seconds.
TeX scratch is created under the validated logs directory, and guard
fixtures under explicitly checked `/tmp`, independently of ambient TMPDIR.

`code/reproduce_zip.py` validates the actual supplied archive against the
trusted frozen source package before executing any extracted code. It then
extracts independent normal and optimized source copies and runs both builds.
It compares all member bytes and metadata, complete ZIP bytes, PDFs, four
receipts, and `build_checks.json`. Exactly seven top-level files are expected
from each build: one PDF, one ZIP, four receipts, and one build-check file;
`logs` is the only top-level directory. It verifies that both extracted
source trees, the trusted source tree, and the input archive remain unchanged.
The original archive must match both rebuilt archives, not merely the two
rebuilds each other. Standalone ZIP replay compares six original artifacts
(the ZIP, PDF, and four receipts) and all seven outputs between the two
rebuilds. Supplying `--original-build-dir` additionally compares all seven
outputs, including the external `build_checks.json`, against the original
build directory and checks that those original files stay unchanged. The
replay receipt distinguishes these counts explicitly. The final validation
uses this stricter mode. A manifest is an integrity record, not a signature
or proof of authorship.

The current guard suite exercises 241 finite cases, listed in its receipt.
These include domain/CLI failures, fixed numeric caps, assertion-free
validation, hostile Python environment variables, output reuse and symlinks,
manifest corruption and completeness, source-size/entry budgets, ZIP path
traversal and duplicates, archive metadata, and explicit temporary parents.

## Commands

Run in the source directory with the pinned Python dependencies available:

```sh
python -B -X int_max_str_digits=640 code/exact_counts.py
python -B -X int_max_str_digits=640 code/algebra_checks.py
python -B -X int_max_str_digits=640 code/saddle_diagnostics.py
python -B -X int_max_str_digits=640 code/guard_tests.py
python -B -X int_max_str_digits=640 -O code/guard_tests.py
python -B -X int_max_str_digits=640 build.py --verify-only
```

The four check commands print deterministic JSON. Their optional `--output`
paths must be new files outside the source package. The README gives the
full build and actual-archive replay commands. Replay is tested on the
recorded installed toolchain; different TeX installations can produce
different PDF bytes without changing the mathematics. Installed Python
packages are pinned in `requirements.txt`. Timings are excluded from receipts.
