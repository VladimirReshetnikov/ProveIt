# Report179: lazy closed walks in growing dimension

This package accompanies the research article on OEIS A328716, the number of
n-step closed walks in Z^n with steps 0 and the positive/negative coordinate
unit vectors. It contains the PDF, editable LaTeX source, exact standard-library
verification, optional SymPy/mpmath diagnostics, and an offline deterministic
builder. The known exact formula and leading equivalent are credited. No open
problem resolution, worldwide priority, or certified finite-input inverse
calculator is claimed.

## Mathematical content

- Every fixed asymptotic order, with a finite cumulant/Gaussian coefficient
  algorithm and the first three explicit corrections
- An absolute complex-uniform marked expansion, including zeros of its leading
  amplitude
- Every fixed weighted l1 probability correction to the parity-conditioned
  Poisson zero-step law
- Occupied-axis Gaussian fluctuations and a product weak limit with the residual
  Poisson variable, plus the constant parity-dependent occupation mean offset
- Parity-sensitive inverse carriers with an eventual global integer bracket of
  width at most one
- A compact proportional length/dimension extension, with a moving-parameter
  approximation and a fixed-law limit only when the ratio and parity stabilize

Every expansion is for a fixed truncation order. Constants and onsets are
non-effective here. No convergence of the infinite series, extreme-ratio
uniformity, fixed-dimensional implication, or continuous-Gaussian total
variation limit is asserted.

## Quick verification

Use Python 3.10 or newer. From an extracted package directory:

```
python -S -B code/verify.py
python -S -B -O code/verify.py
python -S -B guard_tests.py
python -S -B -O guard_tests.py
python -S -B test_build.py
python -S -B -O test_build.py
python -S -B verify_manifest.py
```

The last command applies to the complete release ZIP, which contains
SHA256SUMS.json. The authoring source directory itself is not a finalized
release and has no manifest. Checks are explicit runtime validations and remain
enabled under optimization. Commands do not modify package reference data.
See README_CODE.md for exact test ranges, algorithms, and regeneration commands.

## Rebuild the deliverables

A working TeX installation providing pdfTeX, pdfLaTeX, kpsewhich, and the packages
used by Report179.tex is required. The builder performs no installation or
network access and always disables TeX shell escape. Use a new sibling directory
whose parent already exists:

```
python -S -B build.py --output ../rebuild-one
python -S -B -O build.py --output ../rebuild-two
```

The output path must not already exist, even as a dangling symlink, and must be
outside the source package. The builder refuses symlinked directory components,
checks an explicit source inventory, validates an extracted release's manifest,
and publishes exclusively. It runs the mathematical checks and guard tests in
ordinary and optimized modes and requires equal results. TeX auxiliary files
must stabilize, and unresolved references, overfull boxes, and missing glyphs
are rejected. A successful build publishes:

- Report179.pdf
- Report179.tex
- Report179.zip
- ARTIFACTS.json with the three artifact byte counts and SHA-256 digests

Private temporary caches isolate TeX/Python overrides. ZIP order, entry times,
and permissions are fixed. The same sources and installed Python/TeX stack
produce byte-identical PDF and ZIP files. Different software versions may
produce different bytes.

SHA256SUMS.json detects missing, altered, or unexpected files, symlinks, special
files, malformed entries, and empty/unexpected directories. It is an integrity
inventory, not a digital signature. Path protections do not make the builder a
general sandbox against hostile processes concurrently replacing directory
inodes. Read the code before running any third-party package.

## Evidence and its limits

The exact core compares independent enumeration routes for 52 diagonal sizes,
including n=0..41 and selected sizes through n=201; it also checks joint
zero-step/occupation counts. Independent cumulant and formal-expansion
algorithms verify the displayed coefficient identities. Decimal diagnostics
reproduce the recorded count, total-variation, and occupation examples without
requiring site packages. Their arithmetic is high precision, not
outward-rounded interval certification.

Optional independent SymPy/mpmath programs are isolated under optional/; their
reference JSON output is under data/. They are not imported by the standard-library core or needed
by the builder. Numerical residual stabilization is supporting evidence, not a
proof of the analytic remainders or an effective starting threshold.

SOURCE_AUDIT.md records source attribution, bounded earlier-report comparisons,
and novelty limitations. Copyrighted third-party book/article PDFs and private
research notes are not included. Nothing has been submitted to the OEIS or
published to an external repository by this package.
