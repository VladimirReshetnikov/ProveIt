# Reproducibility and verification

## Requirements and scope

Python 3.10 or later, with only its standard library, suffices for the complete
core verifier, corruption guards, manifest verifier, and packaging logic. The
PDF additionally needs an installed pdfLaTeX/TeX Live distribution with the
packages used in Report179.tex. No network, downloaded code, optional CAS, or
shell escape is used by a build. Optional SymPy/mpmath scripts are isolated in
optional/ with separately pinned requirements.

Exact computations certify the finite algebra and counts tested. Decimal and
mpmath calculations are high-precision diagnostics, not interval bounds. The
analytic fixed-order remainder and distributional theorems are proved in the
manuscript; finite tests do not substitute for those proofs.

## Core commands

Run these from the package root. The -S switch disables site-package loading;
-B prevents Python cache writes. Checks use explicit exceptions, not Python
assert statements, and remain effective under -O.

```
python -S -B code/verify.py
python -S -B -O code/verify.py
python -S -B guard_tests.py
python -S -B -O guard_tests.py
python -S -B test_build.py
python -S -B -O test_build.py
```

The verifier checks:

- All 20 OEIS terms, n=0,...,19, against exact binomial-convolution counts and
  the literal 20-term manuscript prefix
- 52 exact count cases: n=0,...,41 and n=60,61,80,81,120,121,160,161,200,201,
  against an independent Fraction recurrence derived from the Bessel Riccati
  equation
- Ten joint zero-step/occupied-axis cases: n=0,1,2,3,20,21,60,61,120,121;
  nonempty-axis decomposition against the zero marginal, with occupation
  moments additionally checked by dimension deletion when n>=2
- Cumulants 1,...,8 from the Riccati derivation against differentiated Bessel
  ODE raw moments and the moment-to-cumulant recurrence
- Relative coefficients c0,...,c3 from the finite partition formula against
  a separate formal exponential differential recurrence and Gaussian moments
- Centered probability corrections Q1,...,Q3, plus the closed c1, c2 and Q1
  formulas, and agreement with the bundled independent symbolic references
- Three pinned SHA-256 reference/provenance files
- 85-digit standard-library Decimal recalculation of the saddle constants,
  parity corrections, and eight finite-n count, marked-PGF, truncated
  total-variation, and occupation diagnostics at n=20,21,40,41,80,81,160,161

The finite-n TV diagnostics truncate the limiting Poisson sum after n+100,
matching the reference experiment. They are not certified total-variation
bounds. The optional script additionally tests complex amplitude cancellation
and joint characteristic functions; the core checks the hash and symbolic
coefficients of that reference, but does not redo its complex numeric tests.

## Exact algebra and regeneration

code/exact.py implements sparse Laurent polynomials over Fraction with variables
(b,v,j,y), where only b may have negative exponents and y represents it in the
Gaussian expansion. Polynomial output is a sorted list of exponent vectors and
canonical rational strings. No eval, CAS, binary floating point, or removable
assertion is needed. The coefficient functions accept arbitrary fixed orders;
Stirling coefficients are generated from Bernoulli numbers, not a truncated
hardcoded list. Automated identity comparisons are run through order three.
Higher requested orders can be computationally expensive.

```
python -S -B code/regenerate.py --compare data/certificates.json
python -S -B code/regenerate.py --compare data/certificates.json --output /tmp/new-report179-certificates.json
```

The second command requires a new file outside the package; its parent must
already exist. Existing files, symlinked parents and traversal paths are
rejected. Without --output the command writes no file. The committed
certificate is intentionally never replaced by regeneration.

## Build PDF, TeX and deterministic ZIP

Choose a new output directory outside the source or extracted package. Its
parent must already exist.

```
python -S -B build.py --output /tmp/report179-build-one
python -S -B build.py --output /tmp/report179-build-two
cmp /tmp/report179-build-one/Report179.pdf /tmp/report179-build-two/Report179.pdf
cmp /tmp/report179-build-one/Report179.zip /tmp/report179-build-two/Report179.zip
```

The builder first requires an exact explicit source inventory, then snapshots
those bytes into a private temporary package. It runs every core verifier and
guard in both normal and optimized modes with -I -S -B, compares their result
objects, and records the evidence. It compiles in a separate clean TeX working
directory, with -no-shell-escape and restricted TeX input/output settings. At
least two LaTeX passes are run; at most six are allowed until aux/toc/out bytes
stabilize. Unresolved or multiply-defined references/citations, overfull boxes,
missing glyphs, invalid PDF signatures, and nonconvergent auxiliary files fail
the build. If the installed TeX format is unavailable, a private format and
font map are initialized from the installed TeX distribution.

SOURCE_DATE_EPOCH=1790985600, UTC, private caches and fixed ZIP metadata control
reproducibility. Archive names are sorted, entries are stored without
compression, and every file has fixed timestamp and permissions. Identical
sources and the same installed Python/TeX stack are expected to give
byte-identical PDF/ZIP outputs; cross-version identity is not claimed.

Publication exclusively creates the requested output directory only after all
checks pass. Existing files, directories and dangling symlinks are refused;
source descendants, traversal paths, and symlinked parents are refused.
A concurrent creator of the destination is preserved. The builder does not
clean or overwrite source/output trees. This is defensive local packaging,
not a sandbox for hostile TeX or a guarantee against arbitrary concurrent
filesystem replacement.

The output directory contains Report179.pdf, Report179.tex, Report179.zip and
ARTIFACTS.json (hashes and lengths). The ZIP contains the source, PDF, exact
certificate, references, optional scripts, generated check summaries,
generated/BUILD_INFO.json and SHA256SUMS.json. It omits logs, temporary files,
caches and empty directories. --extended is a compatibility alias; all stated
checks already run in an ordinary build.

## Manifest and hostile-input guards

After extracting the ZIP into a clean directory:

```
python -S -B verify_manifest.py
```

The manifest covers every packaged file other than itself, and rejects added,
removed or modified files, unexpected/empty directories, symlinks, special
files, cache files, path traversal, malformed hashes, duplicate JSON keys and
nonfinite JSON constants. An intact extracted release can itself be rebuilt.
SHA-256 detects accidental alteration; replacing both the data and its manifest
is not cryptographic authentication of authorship.

The guard suite deliberately corrupts count, cumulant, correction, diagnostic,
schema, provenance and manuscript fields; it checks strict literal parsing,
normal/-O equivalence, and byte-identical non-destructive regeneration.
test_build.py exercises 162 isolated build/manifest checks (42 accepted cases,
120 rejected cases), including an ordinary simulated build, optimized-result
disagreement, failed compilation, destination races, deterministic archives,
symlinks/FIFOs, source-inventory changes and compiler-log defects. These are
simulated compiler tests; the real builder separately invokes TeX.

## Provenance

The 20-term sequence transcription is traced to the official OEIS repository
URL in data/PROVENANCE.json and the source audit. data/walk_checks.json and
data/independent_checks.json preserve the original independent calculation
outputs. Their byte hashes, together with the provenance hash, are pinned in
code/verify.py and incorporated into the regenerated certificate. This records
which finite evidence was checked; it does not make a priority claim.
