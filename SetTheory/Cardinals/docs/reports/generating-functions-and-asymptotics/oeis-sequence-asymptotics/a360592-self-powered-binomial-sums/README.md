# Report 230: Corrected Poisson endpoint expansions

A standalone 30-page article and reproducible source package for the self-powered
binomial family a_p(n), including OEIS A360592, A360479, and A360747.

## Results

- Exact Poisson reduction and global tail bounds
- Every fixed algebraic order for fixed integer p>=2
- Separate critical p=1 resummation, half-power coefficients, and no odd quarter powers
- Canonically labeled directed-graph interpretation with an inactive-vertex defect
- For p>=2, weighted density remainders, mean/variance refinements, and two sharp
  residue-conditioned Poisson total-variation laws
- Explicit finite-model Newton and convergent local Lagrange inverses
- Exact monotonicity, qualified exact-range recovery, and two-ceiling threshold envelopes

The three observed OEIS leading equivalents remain valid. Their intended higher
coefficients disagree with the proved coefficients. The observations are not
verified latest revision histories. Broader priority remains unresolved.
Classical Poisson, Charlier, root-filter, Taylor, Newton, Lagrange and Lambert-W
machinery is credited and the required identities are proved in the article.

Important scope: fixed p and fixed order only; no secondary exponential sector,
optimal truncation, growing-p theorem, effective inverse onset, or p=1 marked-law
claim. Transcendental diagnostics are not interval-certified. In particular,
the p=3 t^12 truncation at n=10000 still has about -66% relative error.

## Contents

- `Report230.pdf`: rendered article
- `article.tex`, `sections/`: editable TeX source
- `code/`: Fraction-only core, optional mpmath diagnostics, tests and checked outputs
- `SOURCES.md`: public source and retrieval qualifications
- `build.py`: frozen-inventory verification and deterministic rebuild
- `MANIFEST.sha256`: SHA-256 of every payload file except itself

## Reproduce

Python 3.10+ is recommended; checked with Python 3.12.14. Exact tests need only
the standard library. Use `-B` so imports do not add caches to the frozen tree.

```sh
python3 -B code/selftest.py
python3 -B -O code/selftest.py
python3 -B code/endpoint.py coefficients --p 2 --order 4
python3 -B code/endpoint.py critical --order 4
python3 -B build.py --verify-only
python3 -B build.py --output ../rebuilt
```

Optional numerical tests require mpmath 1.3.0 (listed in
`code/requirements-optional.txt`). Install it in an environment of your choice,
then run:

```sh
python3 -B code/selftest.py --numerical
python3 -B code/diagnostics.py suite --deep
python3 -B -O build.py --output ../rebuilt-optimized --numerical
```

The build output must be a new path outside the package; existing paths and
symlink paths/ancestors (including dangling symlinks) are rejected. Source hashes
and inventory are verified before work, including rejection of unlisted files,
unexpected directories, and symlinks. Outputs do not modify source files.

The PDF requires pdfTeX/pdfLaTeX and the standard packages named in article.tex.
The checked toolchain is pdfTeX 1.40.26 (TeX Live 2025/dev/Debian), with Latin Modern
fonts. The builder generates a private format and cache, compiles three passes
without shell escape, and rejects layout/reference warnings. It requires the
rebuilt PDF to match the frozen PDF byte for byte. Another TeX release may produce
different bytes; a mismatching PDF is preserved with a distinct name for
inspection, and the build stops rather than claiming identity. Manual TeX
compilation remains possible on other toolchains.

Successful builds produce Report230.pdf, Report230.zip, build_checks.json and
logs. ZIP ordering, timestamps, modes, and compression are fixed. The ZIP contains
exactly the frozen source package, including its original checked outputs and
PDF; transient build logs are outside the archive. Normal and optimized builds
with the same options produce identical PDF and ZIP bytes on the checked
Python/TeX toolchain. Reproducing `--numerical` additionally requires byte-identical
JSON diagnostics on the documented mpmath version.

See code/README.md for commands, exact interfaces, active resource caps, the
complete-sum versus central-window distinction, and inverse rounding caveats.
