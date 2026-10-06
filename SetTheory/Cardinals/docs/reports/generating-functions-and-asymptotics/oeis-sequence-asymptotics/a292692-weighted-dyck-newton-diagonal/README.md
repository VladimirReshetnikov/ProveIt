# Report 142: All fixed orders on the interior Newton-ratio range

This offline companion accompanies Report142.pdf and its complete LaTeX
source. The article proves the fixed-order expansion uniformly on each
compact subset of 0 < m/N < 1, gives a finite coefficient recursion, and
keeps the inverse uncertainty inside integer ceilings. The finite exact
checks here support the algebra. They do not prove the uniform analytic
remainders or supply effective remainder constants.

The unchanged Report141 source and PDF are included under foundation141/.
Both remain byte-for-byte identical to the foundation release. Their
narrower statements retain their original scope; the extension is in
Report142. No Report141 computational files are duplicated here.

## Quick start

Requirements: Python 3.11 or newer. Exact second-correction replay also needs
SymPy; this release was tested with Python 3.12.14 and SymPy 1.14.0. The
remaining calculations and verifier use the Python standard library. PDF
rebuilds need pdfTeX/pdflatex, the packages named by Report142.tex, Latin
Modern and TeX font maps. The tested engine is pdfTeX 1.40.26 (TeX Live
2025/dev/Debian). No network is used during verification or reproduction.
Dependencies must already be installed; the companion never installs them.

Every executable rejects non-isolated Python before importing anything
except built-in sys. Always use -I; -B is also shown explicitly. This avoids
unsealed local import-shadowing during normal verification.

These are absolute-path examples. Replace /home/alice/report142 with the
absolute bundle directory. Ensure /home/alice/results already exists and
every output named below is absent, even as a symlink. Outputs must be
outside the bundle. Do not reuse output paths or place outputs in this tree.

    python -I -B /home/alice/report142/verify.py check
    python -I -B /home/alice/report142/verify.py replay --output /home/alice/results/report142-replay
    python -I -B -O /home/alice/report142/verify.py replay --output /home/alice/results/report142-replay-optimized
    python -I -B /home/alice/report142/verify.py selftest --output /home/alice/results/report142-selftest
    python -I -B /home/alice/report142/verify.py build --output /home/alice/results/report142-build
    python -I -B /home/alice/report142/verify.py pack --output /home/alice/results/Report142.zip
    python -I -B /home/alice/report142/verify.py reproduce --output /home/alice/results/report142-reproduction

check validates the closed inventory, all digests and the complete nested
fixture schemas. It also checks the unchanged foundation source and PDF
against their pinned digests. replay independently recomputes the new exact
results, compares them with the sealed fixtures, and creates its output
directory only after all comparisons pass.
It never repairs or rewrites fixtures. selftest works on disposable external
copies and exercises deliberately malformed and rehashed false inputs.

build creates a clean external TeX environment, rebuilds the format, compiles
twice, rejects listed layout/reference warnings and reports whether its PDF
matches the frozen PDF bytes. reproduce runs the self-tests and two clean
PDF builds, requires identical build bytes and agreement with the frozen
PDF, and checks fresh ZIP extraction/repacking. A different TeX toolchain
may produce different PDF bytes from the same mathematical source.

pack writes stored, uncompressed ZIP entries in sorted order with fixed
timestamps and permissions. The ZIP has the single top-level report142/
directory. No generated logs, caches or results belong inside the bundle.

## Exact computations

code/second.py regenerates the first and second correction from the defining
saddle and endpoint generating functions. The Gaussian-removed exponential
is obtained by the coefficient recurrence n E_n = sum j F_j E_(n-j), rather
than by fitting sequence values. The kernel's finite-product corrections,
uniform-root moments, shifted unknown and opposite endpoint are combined
symbolically. Euler derivatives of the bivariate generating functions give
the required principal and geometric moments. Only after this derivation
are the stated closed formulas compared with the regenerated values.

The second-order outputs include r2(s), D2(0,0;s), B2(s), and

    b2 = -(30800095 + 3912441 sqrt(17))/80494592
    lambda2 = -(4940681 + 601183 sqrt(17))/10061824

The saddle coefficient is in powers of m^-1; the quotient coefficient is
in powers of N^-1. On N=2n, m=n, the quotient contribution is r2(s0)/4,
where s0=(1+sqrt(17))/8. The factorial second coefficient is 9/512. The
replay checks these scalings and the zero-shift/zero-atom cancellations.

code/finite.py uses integer and Fraction arithmetic independently of SymPy:

- top_coefficients(order) constructs the top ordinary coefficients by exact
  polynomial summation, at any nonnegative fixed order. The fixtures take
  order 7, check all 28 boundary zeros, divisibility by the falling factorial,
  degree bounds, and 176 comparisons against the direct recurrence for n≤21
- The frozen inverse checks all 40 square-root coefficients, all 860
  bivariate basis coefficients through degree 40, and 360 actual rational
  coefficient identities at s=1/5, 1/2, 4/5 and 19/20 through degree 12
- saddle_coefficients(s, ell, r, order) implements the finite Gaussian
  algorithm at any nonnegative fixed order and exact rational s in (0,1).
  The fixtures use order 3, four saddles and five shifts each. They check
  parity, the first closed coefficient, the unshifted second coefficient,
  normalized quotient multiplication and the zero-shift positive-order zeros

The executable global quotient reconstruction computes r1 and r2. The
article specifies the complete all-orders r_j recursion; no claim is made
that this companion computes every r_j symbolically at arbitrary order.
Likewise, finite convolution checks are not a substitute for the article's
bounded-extension, parameter-drift and nested-compact remainder proof.

## Fixture representation and integrity

checks/fixtures.json is fully typed, closed and exact. Polynomial lists use
ascending powers with canonical rational strings; rational functions have
monic denominators. A quadratic-field pair [a,b] denotes a+b sqrt(17).
Counts and indices are JSON integers, never booleans, floats or strings.
All nested objects and row shapes are explicitly validated. There are no
floating-point tolerances or sequence-fitting diagnostics in Report142's
new fixture. No Report141 numerical fixtures are included in this bundle.

manifest.json covers every payload byte except itself. The allowed file and
directory inventory is hard-coded. The foundation source and PDF SHA256 digests are also
pinned independently. Unknown or missing files, symlinks, nonregular files,
duplicate JSON keys, unknown nested fields, malformed rationals and arrays,
JSON floating-point tokens (including overflow such as 1e999), NaN/Infinity
and boolean integer substitutions are rejected. A hash-valid but false
mathematical fixture is rejected by replay.

Self-tests exercise structural and mathematical mutations, the foundation
pin, all executable entrypoints' early import guards under normal and -O
startup, external-output containment, ancestor symlinks, parent traversal,
existing target preservation, double-leading-slash aliases, normal/-O
byte-identical replay, fresh archive extraction and unchanged original bytes.
Every output command preflights its target before loading computational
modules or creating output. Outputs are created exclusively.

The seal is an integrity/reproducibility mechanism, not an authenticated
signature or a sandbox for hostile code. A person who changes the verifier
and matching hashes can create a different bundle. Obtain a trusted archive
hash and review source where needed. The tool assumes a trusted local
workspace; it does not promise adversarial filesystem race isolation.

For maintainers, seal validates the payload and schemas and writes a
proposed manifest to an absent external file. It never installs that file
or changes the bundle. After authorized edits, review and install it
manually, then rerun replay and reproduce:

    python -I -B /home/alice/report142/verify.py seal --output /home/alice/results/report142-proposed-manifest.json

Public provenance is in SOURCES.md. Exploratory notes and intermediate
audit files are not needed and are not included.
