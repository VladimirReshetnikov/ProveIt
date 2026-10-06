# Report174: rectangular maximum-density kings on a horizontal cylinder

This package accompanies **Report174**. The board has `2h` open rows and `2w`
cyclic columns. Its cells are labeled; no rotations or reflections are identified.
`A(h,w)` is the number of placements of `hw` mutually nonattacking kings, for
positive integers `h,w`.

The report develops the aspect-ratio transition at `w/h = log(2)`, including
subcritical, supercritical and critical-window formulas. It also discusses
fixed-height spectral consequences, rational-ray inversion, historical scope,
and the limitations of the claims. Consult the report's bibliography and
priority discussion for the earlier exact encodings and spectral results.

## Contents

- `Report174.pdf`: the compiled report
- `Report174.tex`: complete LaTeX source, including its bibliography
- `companion/run_checks.py`: bounded standard-library verification runner
- `companion/exact_checks.py`: independent geometric, trace and integer-algebra checks
- `companion/symbolic_checks.py`: exact rational and formal-polynomial identities
- `verification.json`: the results from the packaged verification mode
- `build_info.json`: recorded toolchain, recipe and verification mode
- `build_package.py`, `verify_package.py`, `package_tools.py`: build and integrity tools
- `test_package_tools.py`: adversarial integrity and no-clobber tests
- `manifest.json`: SHA-256 and byte length of every payload file

No downloaded articles, book scans, third-party source extracts, private research
notes or unrelated working files are included. The Python checks are original
companion code. No CAS, NumPy or SciPy installation is required.

## Prerequisites

Python **3.10 or newer** is sufficient for verification. A current TeX Live or
MiKTeX installation providing `pdflatex` and the packages imported by
`Report174.tex` is required only to build or fully replay the PDF. The build does
not download software or sources and disables TeX shell escape. TeX caches are
confined to its temporary workspace. If the installed distribution lacks a
generated pdflatex format, the build initializes a local format and font map
from installed files, with no global or home-directory writes. The original
build's versions are listed in `build_info.json`.

Commands below are run from the extracted `Report174` directory. Replace
`python3` with your local Python command if necessary.

## Run the checks

```sh
python3 companion/run_checks.py
python3 -O companion/run_checks.py
python3 companion/run_checks.py --no-diagnostics
python3 companion/run_checks.py --extended --output ../extended-results.json
python3 companion/symbolic_checks.py --max-defect 16
python3 test_package_tools.py
python3 -O test_package_tools.py
```

The default runner prints deterministic, sorted JSON. `--output` creates a new
file exclusively and refuses to replace an existing file. All mathematical
correctness guards remain executable with `python -O`; they do not use Python
`assert` statements. A failing identity exits unsuccessfully.

The default suite checks:

1. All `1 <= h,w <= 6`: an exact row-mask maximum-cardinality DP using geometric
   attacks, versus an independently implemented binary-threshold trace sum
2. Independent pairwise-distance subset enumeration whenever `h*w <= 5`, plus
   the tiny-height and tiny-width closed formulas, including physical width two
3. Every binary word of lengths 1 through 7: integer `M = E0 E1`, Gram and tree
   trace identities through power four; every marked run's multiplicity and
   first two rooted branch moments; a third-moment bound
4. Fixed heights 1 through 5: smaller-Gram dimension bounds, complementary-word
   spectral multiplicities, and the exact reduced generating-function
   denominator, checked for no cancellation and squarefreeness using rational
   polynomial arithmetic
5. Alternating words for primes 5, 7 and 11: exact characteristic polynomials
   attaining the dimension bound, with a reported finite-field irreducibility
   certificate (no numerical root fitting)
6. Exact rational identities for `c1` and `c2`, including the explicit `P6/P8`
   expression; the Schur/log/exponential Taylor coefficients; 28,672 ordered
   boundary-composition pairs at defects 0 through 12; the critical `a`, `b`,
   `H`, `J(0)` and Euler–Maclaurin constants

`--extended` increases rectangles to `1 <= h,w <= 7`, words through height 9,
subsets to `h*w <= 6`, fixed-height generating functions through height 6,
sharpness primes through 19, and the composition cutoff to 16 (589,824 pairs).
The defaults are intentionally bounded. On the build machine the default run
takes about a second and the extended run takes about 30 seconds; speeds vary.
There is no unbounded search or mandatory optional-CAS path.

### Exact counts and marked-star diagnostics are different

`A(h,w)` is calculated exactly only by the finite geometric and trace checks.
`S(h,w)` is the explicitly evaluable **marked-star proxy**. The JSON reports both
on small boards and checks that they are not accidentally the same data series.
Larger scalar tests evaluate only `S/h^w`, at actual integer-compatible critical
parameters. They never label this as a computation of `A/h^w`.

The critical proxy constant is `J_star(t)`. The report's true-count formula adds
`4 log(2) G(t)`; at the center this adds exactly 4. The numeric residuals are
illustrative diagnostics, without a pass/fail convergence threshold. They do not
prove the asymptotic remainder, uniformity, distributional statements or inverse
first-crossing brackets. Floating diagnostic digits can depend on the platform's
math library. Integer and rational algebra checks are exact.

## Fresh, isolated build

Choose an output directory that does **not** exist:

```sh
python3 build_package.py --output ../Report174-build
python3 build_package.py --extended --output ../Report174-build-extended
```

The build copies only an explicit source allowlist into an isolated temporary
workspace, runs the suite in ordinary and optimized Python and compares results,
runs the packaging tests in both modes, and compiles LaTeX **at least twice**, continuing up to six passes if needed
for stable auxiliary files. It rejects unresolved references, overfull boxes and
missing-glyph warnings after stabilization. It then writes the manifest,
checks every payload hash, and creates the complete ZIP.

The output contains:

- `Report174/`: the complete verified package, including `Report174.pdf`
- `Report174.zip`: that entire directory with stable archive ordering/metadata
- `SHA256SUMS.txt`: hashes for the ZIP, PDF and manifest
- `build.log`: command output, outside the distributed package

There is deliberately no overwrite/force option. A failed build leaves a
`BUILD_FAILED.txt` notice and any available log; retry with another new directory.
The default per-command time limit is 300 seconds, adjustable with
`--timeout N` for `1 <= N <= 3600`. The source directory is never modified by the
build itself. The command-line entry points also disable Python bytecode-cache
writes. Write any additional results outside the extracted package if you want
the strict manifest inventory to remain unchanged.

## Verify and replay

Hash verification uses only the standard library:

```sh
python3 verify_package.py .
python3 verify_package.py ../Report174.zip
python3 verify_package.py ../Report174.zip --checks-only
python3 verify_package.py ../Report174.zip --replay
```

The verifier rejects unlisted, missing, changed or symlinked files. ZIP extraction
also rejects duplicates, unexpected paths, symlinks, encryption and oversized
members. `--checks-only` re-executes both Python modes in a temporary directory,
compares exact/symbolic results with the stored results, and needs no TeX.
`--replay` performs the complete multi-pass build in a new temporary directory and
requires every payload byte to match; when verifying a ZIP, its bytes must match
too. Replays are explicit code execution, so use a package from a trusted source.

A fixed source date, omitted PDF timestamps/IDs, stable ZIP timestamps, fixed
permissions and ordering, and clock-free result files make same-toolchain builds
byte-reproducible. Byte-for-byte reproduction across different Python, libm,
TeX/font or zlib versions is not promised. A cross-toolchain mismatch is reported
rather than silently accepted; `--checks-only` still checks the exact arithmetic.
The manifest excludes its own hash and the containing ZIP to avoid circularity.
The outer `SHA256SUMS.txt` records both. Hash consistency detects changes; without
an independently trusted hash or signature it does not authenticate the publisher.

## Mathematical limits

Finite experiments and exact coefficient identities supplement the written
proofs. They do not constitute machine-checked proofs of all board sizes,
all-order asymptotics, uniform analytic error estimates, historical novelty, or a
certified finite-input inverse algorithm. In particular, retain the report's
actual lattice parameter when using refined critical or rounded-ratio formulas.
