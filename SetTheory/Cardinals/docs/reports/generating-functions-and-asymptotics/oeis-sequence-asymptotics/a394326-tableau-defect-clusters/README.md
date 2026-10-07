# Report183

Certified asymptotics for tableau defect clusters, OEIS A394326

## Main result

With a(0)=0, the exact cluster coefficients satisfy

    |a(n) - c*rho^(-n)| <= 2500*(100/63)^n    for every n >= 0,

where

    0.6180397469174016 < rho < 0.6180397783636036,
    0.1838102868 < c   < 0.1838120734.

The growth constant 1/rho is strictly below the golden ratio. The source's
strict golden-ratio and Fibonacci asymptotic equivalents therefore fail;
its weaker observed small relative Fibonacci residual remains compatible.

The report proves the source-to-operator identification, signed trace-class
Fredholm quotient, unique noncancelled dominant pole, explicit error, every
fixed finite spectral order, eventual strict growth from n=600, exact large-y
threshold and two-ceiling inverse bounds, all-order expansions of the bounding
roots, and a local signed span-marker extension. It does not claim all-index
coefficient positivity, a probability law or CLT, a list of later poles,
continuation through the unit circle, or worldwide priority.

No external publication or repository submission is part of this package.

## Files and reading order

1. `Report183.pdf`: the complete mathematical report
2. `Report183.tex`: editable source for the PDF
3. `README_REPRODUCIBILITY.md`: detailed certificate commands, methods, tests,
   dependencies, source attribution and limits
4. `code/` and `data/`: exact verifier programs and proof data
5. `certificates/`: deterministic reference outputs, recomputed by the verifier
6. `generated/`: release verification and build metadata
7. `SHA256SUMS.json`: complete archive file inventory and hashes

The definition and extraction are credited to Morten Brydensholt's
[OEIS record](https://oeis.org/A394326). The inspected implementation is Sean A.
Irvine's [jOEIS translation](https://github.com/archmageirvine/joeis/blob/master/src/irvine/oeis/a394/A394326.java),
Git blob `e59ad7a42e0c96f832b97b6457ea9b5cb1d4a851`. Neither the third-party Java
source nor third-party papers are redistributed. Sources and access limits
are explained in the report.

## Verify without installing numerical dependencies

Python 3.10+ is sufficient. From the extracted archive directory:

```sh
python3 verify_manifest.py
python3 reproduce.py
python3 test_build.py
python3 -O test_build.py
```

The complete mathematical replay uses only the standard library, runs the
normal and optimized verifiers in isolated Python subprocesses, and compares
all eleven generated JSON files with their reference bytes. Default replay
uses temporary storage outside the archive and leaves the extracted package
unchanged. Expect roughly 36 seconds on the preparation machine; timings vary.

All acceptance guards raise explicit exceptions. The mathematical test suites
include deliberate corruptions. The separate build/manifest suite covers 180
acceptance and rejection cases, including malformed JSON, symlinks, path
traversal, altered data, unexpected files, failed compilation, unstable TeX
references, warning detection, output races, and deterministic ZIP metadata.
It simulates compiler calls; the actual release build compiles TeX separately.

The inverse proposals are exact dyadic candidates, not trusted approximate
answers. Every replay verifies their outward interval residuals before use.
Optional regeneration imports mpmath 1.3.0; no mandatory verifier does.

## Rebuild the PDF and clean ZIP

In addition to Python, rebuilding the PDF requires an installed TeX stack with
`pdflatex`, `pdftex`, `kpsewhich`, Latin Modern fonts, amsmath/amsthm/amssymb,
mathtools, geometry, microtype, hyperref, enumitem, booktabs and array. The builder
uses installed resources only; it performs no network operations or package
installation and disables TeX shell escape.

Choose a new output directory outside the extracted archive, whose parent
already exists:

```sh
python3 build.py --output ../Report183-rebuilt
```

The builder verifies the entire input inventory, runs build guards in normal
and optimized Python, recomputes the mathematical certificates in both modes,
compiles in a private temporary TeX workspace until references stabilize,
rejects warnings and layout defects, and creates the PDF, TeX copy and ZIP only
after all checks pass. An existing output path is rejected without alteration.
TeX caches are private. Intermediate files and temporary replay outputs do not
enter the ZIP. `ARTIFACTS.json` beside the three deliverables records their sizes
and SHA-256 hashes.

ZIP entries have fixed order, timestamp and permissions. PDF volatile metadata
is disabled. Rebuilding an extracted archive is byte-identical with the same
source and installed Python/TeX stack; PDF equality across different TeX or font
versions is not promised. The release was also rendered and visually checked
page by page, a check not replaced by absence of TeX warnings.

Hashes detect accidental modifications. They are not signatures or proof of
mathematical correctness if both data and hashes are replaced. Regenerate and
review the mathematical checks when deliberately changing proof data.
