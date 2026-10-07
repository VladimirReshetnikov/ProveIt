# Report187: Hidden Oscillations in Square-Root Factorial Sampling

This package accompanies the mathematical manuscript `Report187.tex` and the
matching `Report187.pdf`. It studies

S(x) = sum(k >= 0) x^sqrt(k) / Gamma(1 + sqrt(k)),

and its integer floors, OEIS A326805. The principal term is 2*x*exp(x), while
the leading absolute discrepancy has an oscillating, unbounded envelope of
order x^(1/8)*(log x)^(3/8). The paper distinguishes fixed-order asymptotics
from exact finite-harmonic decompositions and from numerical evidence.

## Quick checks

Python 3.10 or later is required. The mandatory checks need only the standard
library, require no network, and do not invoke the optional packages.

    python -B reproduce.py
    python -B test_build.py
    python -O -B test_build.py

The first command regenerates the exact coefficient and rational-tail
certificates, runs mathematical corruption guards, and compares normal and
optimized Python output byte for byte with the shipped references. It uses
private temporary storage and leaves this directory unchanged.

If this is an extracted release, verify the entire package first:

    python -B verify_manifest.py

The release manifest covers every other file, including the PDF, TeX source,
code, attributed fixture, certificates and build receipts. It detects
accidental modification; it is not a signature or proof of authorship.

## Build PDF and code ZIP

With an installed TeX distribution providing `pdflatex`, `kpsewhich`, and the
manuscript's packages:

    python -B build.py --output ../report187-release

The output directory must not exist, must be outside the source package, and
must have an existing parent. The builder refuses to overwrite files. It
produces `Report187.pdf`, `Report187.tex`, `Report187_code.zip`, and a small
artifact hash receipt. It runs exact checks and ordinary/optimized build
corruption tests, compiles until auxiliary files stabilize, rejects warnings
and layout defects, creates a full manifest, and verifies the archive input.

PDF and ZIP bytes are deterministic for unchanged sources and the same
installed Python/TeX stack. No cross-version PDF identity is promised. The
compiler runs with shell escape disabled and private caches; the build makes
no network requests. Only run code and TeX from a source you trust.

## What is exact, and what is diagnostic?

- Mandatory: finite Bernoulli/Gaussian coefficient algebra in rational numbers
  and powers of 1/pi; exact rational upper-tail inequalities for n=1,...,34;
  integrity, parameter, corruption, output-safety and packaging checks
- Optional: `mpmath` floor replay and completed-line quadrature; these are
  floating consistency checks, not interval certificates
- Optional: an independently implemented SymPy expansion, compared exactly
  with the standard-library coefficient generator
- Analytic results, including contour estimates and asymptotic remainders,
  are proved in the manuscript; the scripts are not finite-data proofs of
  the theorem or effective onset bounds

See [README_REPRODUCIBILITY.md](README_REPRODUCIBILITY.md) for commands, supported
parameters, the positive-tail derivation, and failure behavior. See
[DATA_SOURCES.md](DATA_SOURCES.md) for attribution and redistribution scope.
