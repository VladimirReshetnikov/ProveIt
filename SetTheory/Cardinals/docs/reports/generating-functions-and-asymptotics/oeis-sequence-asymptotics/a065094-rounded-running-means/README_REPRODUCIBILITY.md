# Reproducing Report186 offline

## Dependencies and scope

Mandatory mathematical verification needs Python 3.10+ and its standard library
only. Every subprocess uses `-I -S -B`, additionally `-O` in optimized mode. No
package installation, network request, CAS, numerical integration or floating
point is used for an exact certificate. Optional mpmath 1.3.0 and SymPy 1.14.0
were used for separately labeled diagnostic comparisons; other versions are not
promised identical diagnostic formatting.

PDF production requires `pdflatex`, `kpsewhich`, and (if no installed format is
available) `pdftex`, plus the installed LaTeX distribution. The manuscript uses
article, fontenc, inputenc, lmodern, amsmath, amssymb, amsthm, mathtools, booktabs,
array, geometry, microtype, hyperref and enumitem. The builder can initialize an
isolated format from the installed distribution. It never installs dependencies.
Missing dependencies are reported as failures, not fetched automatically.

The guarantee is byte-identical PDF, TeX, ZIP and receipt when rebuilding the same
source with the same installed Python/TeX/font stack. It is not a promise of
cross-version or cross-platform PDF identity. Filesystem timestamps, source paths,
user caches and build wall-clock time are not deliberately embedded.

## Read-only verification and exact replay

Run from an extracted archive:

```
python3 -B verify_manifest.py
python3 -B verify_source_data.py
python3 -B reproduce.py --output-dir /existing/parent/replay-one
python3 -O -B test_build.py
```

`verify_manifest.py` checks the complete file set and SHA-256 digests, excluding
only the manifest itself. It rejects duplicate JSON keys, non-finite constants,
unsafe names, missing/extra files, empty directories, caches, symlinks and special
files. A source-only working tree has no release manifest until it is built;
`verify_source_data.py`, the mathematical scripts and the builder still apply.
Hashes are change detectors, not cryptographic proof of the origin of a package.

The replay driver runs six scripts in both modes and compares their exact stdout
bytes to the included references. Normal and optimized outputs are placed in
separate subdirectories, with `RESULT.json` recording their common hashes. It
checks an existing whole-release manifest before replaying. Every output directory
must be new, outside the source, with an existing non-symlinked parent. A failure
before publication leaves no replay output directory. Temporary work is removed.

For individual checks, run the scripts with `python3 -B code/NAME.py` and again
with `python3 -O -B code/NAME.py`. They write JSON only to stdout. Any redirection
should point outside the source package. For example:

```
python3 -B code/formal_series.py --order 12 > /existing/parent/order12.json
```

The generic formal algorithm accepts any fixed nonnegative forward order at the
API level; its CLI verifies displayed coefficients and therefore requires order
at least six. Default order is nine. The polynomial operations are finite and
exact, with explicit unit/constant-term checks. Higher requested orders may cost
substantially more time. Formal cancellation verifies coefficients, while the
credited classical theorem supplies analytic asymptotic validity.

## Isolated release build

```
python3 -B build.py --output /existing/parent/release-one
```

The builder validates the entire source inventory, reads only explicit allowed
files, and copies them to a private temporary workspace. It runs build/manifest
negative tests in both Python modes, runs the exact replay in both modes, and
compiles the copied manuscript. It stabilizes TeX auxiliary files and rejects
undefined citations/references, multiply defined labels, missing characters,
overfull/underfull boxes and reported TeX/package/font warnings. Shell escape is
disabled and TeX's input/output settings are restricted.

The environment has fixed SOURCE_DATE_EPOCH=1790985600, UTC, deterministic Python
hash seed and private HOME/TMPDIR/TeX cache/font directories. PDF dates and trailer
identifiers are suppressed by the manuscript. ZIP entries are sorted, stored
without compression, have timestamp 2026-10-03 00:00:00, and mode 0644. All output
creation is exclusive. Existing paths, dangling links, symlinked parents, path
traversal and output anywhere inside the source are refused. The builder does not
provide a sandbox against a hostile replacement TeX installation or trusted code;
its guards protect normal reproducibility and common path/accidental-corruption
failures. Do not run code from a package whose origin you do not trust.

`generated/BUILD_INFO.json`, `generated/build_guards.json`, and
`generated/verification.json` inside the archive record build parameters and
checks. `ARTIFACTS.json` beside the PDF/TeX/ZIP records their byte counts and hashes.
The release manifest inside the ZIP covers every other package member, including
the PDF and these generated check records. No raw research notes or full third-
party article PDFs/texts are packaged.

## Independent extracted rebuild

Use a fresh directory, extract the produced ZIP, and verify it before rebuilding:

```
mkdir /existing/parent/extracted
python3 -m zipfile -e /existing/parent/release-one/Report186_code.zip /existing/parent/extracted
python3 -B /existing/parent/extracted/verify_manifest.py
python3 -B /existing/parent/extracted/build.py --output /existing/parent/release-two
cmp /existing/parent/release-one/Report186.pdf /existing/parent/release-two/Report186.pdf
cmp /existing/parent/release-one/Report186.tex /existing/parent/release-two/Report186.tex
cmp /existing/parent/release-one/Report186_code.zip /existing/parent/release-two/Report186_code.zip
cmp /existing/parent/release-one/ARTIFACTS.json /existing/parent/release-two/ARTIFACTS.json
```

Extract only a trusted ZIP into a new directory. The commands above describe
same-stack rebuilding; the package does not modify the original extracted files.
An ordinary import from another ad hoc interpreter can create `__pycache__` unless
bytecode writing is disabled before import. Such extra files are intentionally
rejected by the strict source inventory; use the documented `-B` entry points.

## Mathematical checks and limits

The main certificate scales the Laguerre recurrence to integers and iterates both
rounded trajectories to N=10000. Conversion from A to the Bessel coefficient C and
exponential coefficient c uses exact positive Taylor and alternating-series
bounds, integer square-root bounds, and outward integer decimal division. The
published certificate is regenerated byte for byte. The independent audit instead
computes factorial-scaled P_N and T_N from their positive finite sums and uses
quotient/remainder trajectory updates. It independently checks A enclosures,
cone choices, final states and the common width; conversion of C and c is checked
by the primary rational calculation. The exact-data checker verifies official
b-files and prefixes, P's finite sum and sum identity, and the symbolic Casoratian.

Negative mathematical tests deliberately change exact states, endpoints, widths,
OEIS values/indices, forward/inverse coefficients, Casoratian sign and source
receipts. They also check malformed parameters and the elementary interval APIs.
All checks throw exceptions explicitly. Optimization cannot disable them.

The narrow exact rational intervals certify 69 common truncated decimal places
for all six A/C/c values, as checked separately by `check_common_truncations.py`
and recorded in `certificates/common_truncations.json`. Of the displayed 70-place
endpoint pairs, the ceiling-A pair shares only 68 fractional digits and the other
five share 69. Thus the 69-place claim for ceiling A depends on the finer rational
interval, not its broader printed endpoints. A formal
all-orders algorithm does not imply a convergent infinite series. Neither these
programs nor the report supplies a finite onset for eventual log-concavity or
all-order error estimates. Range inversion concerns Y=a_n; arbitrary real
thresholds require the report's two-ceiling envelope and unspecified effective
constants/onset, not a universally correct single rounding rule.

## Optional diagnostics

```
python3 -B optional/diagnostics_mpmath.py
python3 -B optional/diagnostics_sympy.py
python3 -B optional/derive_coeffs_sympy.py
```

The first uses 120-digit floating arithmetic to inspect residuals, asymptotic
truncations and range-inverse errors. It is explicitly not interval arithmetic.
The latter two use SymPy as optional independent symbolic comparisons. They are
not run by the mandatory build and cannot substitute for the exact certificates.
