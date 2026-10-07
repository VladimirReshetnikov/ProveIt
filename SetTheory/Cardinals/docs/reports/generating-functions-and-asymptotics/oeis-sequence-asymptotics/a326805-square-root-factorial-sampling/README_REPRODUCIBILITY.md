# Reproduction and verification

## 1. Minimal exact replay

From the package directory, use Python 3.10 or later:

    python -B reproduce.py

For durable results in a new sibling directory:

    python -B reproduce.py --output-dir ../report187-replay

The output parent must exist. Existing outputs, symlinked directories, path
traversal and an output inside the source tree are rejected. No files in the
package are edited. Temporary storage is removed even after failed checks.
The same scripts are run using isolated Python (`-I -S -B`), once ordinarily
and once with `-O`. Every resulting byte must equal the matching file under
`certificates/`. A changed reference is not silently regenerated or accepted.

The generated `RESULT.json` records the reference hashes and provenance check.
The shipped mandatory reference certificates are:

- `formal_coefficients.json`: exact d_(m,0),...,d_(m,6), for m=1,2
- `positive_tails.json`: exact positive-tail bound for each n=1,...,34, with
  rational numerator and denominator and a strict comparison to 10^-35
- `mathematical_guards.json`: accepted boundary cases and deliberate rejection
  of malformed inputs, changed coefficients, altered tail values, failed
  thresholds and damaged data receipts

No mandatory computation requires mpmath, SymPy, network access or TeX.

## 2. Coefficient representation and supported parameters

`code/exact_coefficients.py` exposes `coeffs(N,m)`. The result is a list indexed
by j. Each entry is a dictionary indexed by p with a pair of exact Python
`Fraction` values `(a,b)`, representing

    d_(m,j) = sum_p (a + i*b) * pi^(-p).

The implementation uses the B_1=-1/2 Bernoulli convention, builds the logarithm
of the formal saddle factor, exponentiates by the finite recurrence
n*H_n = sum(j=1,...,n) j*L_j*H_(n-j), and applies the Gaussian moments.
It checks d_0,d_1,d_2 against the printed m=1 formulas using explicit errors,
not removable Python assertions.

Supported API inputs are integer order 0<=N<=12 and integer mode 1<=m<=1000.
The bounded implementation contract is a resource/scope guard; it is not a
mathematical limit on the fixed-mode theorem. Boolean values, floats,
Fractions and strings are not accepted as integer parameters. At order zero,
the sole coefficient is exactly 1. Tests cover the upper supported order,
mode endpoints and consistency under truncation.

    python -B code/exact_coefficients.py
    python -O -B code/exact_coefficients.py

Both commands print canonical JSON, without creating files.

## 3. Exact rational positive-tail inequality

Let n>=1 and T>n be integers, put c=1-n/T, and include terms through k=T^2.
For f(u)=n^u/Gamma(1+u), the standard digamma inequality
psi(1+u)>log u and log(n/T)<=-(1-n/T) give

    f'(u)/f(u) <= -c,  u>=T.

Thus f(sqrt(t)) is decreasing for t>=T^2. Integral comparison yields

    sum(k>T^2) f(sqrt(k))
      <= 2 * integral(T,infinity) u*f(u) du
      <= 2 * n^T/T! * (T/c + 1/c^2).

The final expression is a positive rational number. The mandatory code
computes it exactly with `Fraction` and verifies it is strictly below 10^-35
for T=4*n+60 and n=1,...,34. At n=0, S(0)=1 by the limiting convention and the
remaining positive-index terms vanish exactly.

`code/positive_tail.py` exposes `tail_bound(n,T)` for integer 1<=n<=1000 and
integer n<T<=10000. `check_bound` compares a supplied exact Fraction with the
formula and a positive exact threshold, rejecting both altered values and
unmet thresholds. Neither function evaluates Gamma in floating arithmetic.

    python -B code/positive_tail.py
    python -O -B code/positive_tail.py

The exact bound controls omitted positive terms only. It does not control
roundoff in included floating terms, so even a stable floor at two precisions
is not an interval-certified floor. The package makes no such claim.

## 4. Optional diagnostics

Optional dependencies are mpmath and SymPy from their ordinary installed
Python packages. These scripts are never executed by `reproduce.py` or by
the PDF/ZIP builder. They print structured results, including their limitations.
Run each script with `--help` for supported argument ranges.

The quick default floor replay and the full 35-term two-precision replay are
separate modes. The full command recalculates every fixture value at 55 and 75
decimal digits with exact rational omitted-tail bounds. The completed-line
script compares quadrature with the envelope-normalized first-mode expansion
and checks a larger cutoff. Its finite cutoffs and floating quadrature errors
are not rigorously enclosed. The independent SymPy script reconstructs the
formal saddle factor separately, then checks symbolic equality against the
standard-library result.

Run the complete attributed floor replay and independent symbolic check:

    python -B optional/replay_oeis.py --full --precisions 55 75
    python -B optional/diagnostics_sympy.py --order 4 --modes 1 2

Run the quick or full completed-line diagnostic:

    python -B optional/stable_modes.py
    python -B optional/stable_modes.py --full

The full mode run covers L=20,40,80,120,200,400,800 and m=1,2,3 at 70 digits
with cutoffs 14 and 16. The quick run uses L=20,80 and m=1,2 at 50 digits
with cutoffs 10 and 12. Shipped JSON records are the freshly run full OEIS
replay, exact SymPy check and both quick and full completed-line diagnostics. They are
labeled by scope and dependency version. They are not mandatory certificates
and are not compared byte-for-byte across dependency versions.

See `optional/README.md` and each script's `--help` for further options.

A missing optional package stops that diagnostic with a clear error; it does
not invalidate or bypass the mandatory standard-library checks. Agreement
between floating precisions or cutoffs is evidence of consistency, not proof
of an error bound, all-order theorem, or eventual onset.

## 5. Adversarial checks and optimization

    python -B code/test_mathematical_guards.py
    python -O -B code/test_mathematical_guards.py
    python -B test_build.py
    python -O -B test_build.py

The build/manifest tests use isolated synthetic fixtures and simulated TeX
output; they do not invoke TeX or overwrite the source package. They exercise:

- Changed, added, missing and symlinked package files; special files and caches
- Duplicate JSON keys, non-finite constants, malformed digests and unsafe paths
- Manifest mismatches, altered source receipts and complete inventory checks
- Existing outputs, symlinked parents, path aliases, output races and output
  locations within the source package
- Deterministic archive order, timestamps, permissions and stored compression
- Ordinary/optimized disagreement, non-PASS verifier output and failed builds
- Unstable TeX auxiliaries, undefined references, warnings, layout defects and
  invalid PDF signatures
- Source code free of removable `assert` statements

A PASS reports what the tests actually exercised. Synthetic compiler tests do
not claim an actual PDF compilation; `build.py` performs the real compilation.

## 6. Offline build and inventory

    python -B build.py --output ../report187-release

The builder has a closed `SOURCES` tuple in `build.py`. That tuple is the
source allowlist; files not explicitly included are rejected rather than
silently copied. The only generated release additions are the PDF and
`generated/verification.json`, `generated/build_guards.json`,
`generated/BUILD_INFO.json`, followed by `SHA256SUMS.json`. The manifest lists
all other files and does not hash itself. An extracted release can rebuild
only after its complete inventory and hashes pass verification.

TeX runs with a fixed SOURCE_DATE_EPOCH, UTC metadata, private format/cache
locations, no inherited TEXINPUTS/PYTHONPATH and no shell escape. Auxiliary
files must stabilize and the log must be free of warning/layout defects.
ZIP entries are sorted, use fixed timestamps and mode 0644, and are stored
without compression to avoid compressor-version variance. The same source
and installed Python/TeX stack produce byte-identical outputs. Different
Python/TeX versions, fonts or packages may legitimately change PDF bytes.

For an extracted release:

    python -B verify_manifest.py
    python -O -B verify_manifest.py

Hashes detect accidental modification, not replacement of both a file and
its manifest. The source list is narrow by design: no full OEIS export,
third-party PDFs, raw research notes, transient logs, Python caches or
unrelated source files are distributed. The clean package can be run wholly
offline after Python, the optional packages if used, and TeX are installed.
