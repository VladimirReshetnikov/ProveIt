# Certified extremal windows for unknot recognition

Research contribution for `VladimirReshetnikov/ProveIt`, October 7, 2026.

**Main article:** [`article/manuscript.pdf`](article/manuscript.pdf), with complete
LaTeX source in [`article/manuscript.tex`](article/manuscript.tex).

This package adds exact low-degree Khovanov windows, mirror windows, and a
three-outcome recognition interface. The retained complex contains a one-degree
halo. Exhaustive unit cancellation happens **before** truncation. The halo is
never reported as true homology.

The main proof is a minimal-truncation domination theorem. Combined with an
explicit description of the radical of the dotted matching category, it
transfers the Kelomäki–Schütz binomial bounds to arbitrary exhaustive unit-pivot
policies. For a certified nice order of girth W and output depth k, the bound is

```
poly(n,W) * 2**O(W) * (sum(comb(n,j), j=0..min(n,k+1)))**3.
```

This gives `n**O(log n)` for windows with `k=O(log n)` and `W=O(log² n)`, and
for adaptive rejection when the first discrepant endpoint degree has that
shallow depth. It is **not an unrestricted quasi-polynomial unknot recognizer**.
The exact Reidemeister-II padding theorem shows that raw discrepancy depth can
be linear even at constant girth. A positive result for every unknot also
requires more than shallow agreement.

## Run

Python 3.10+; standard library only. Tested here on CPython 3.13.5 (see exact
runtime metadata in `results/benchmark.json`). Run from this directory:

```bash
python -m unittest discover -s tests -v
python -m experiments.validation
python -m experiments.benchmark --repeats 3
python -m unknot_windows examples/torus_3_4.json --depth 0
python -m unknot_windows examples/torus_3_4.json --adaptive
```

The first torus example returns `UNKNOWN`; the adaptive example returns
`NONTRIVIAL`. CLI defaults impose a cooperative 60-second ceiling and a
20,000-object ceiling. These are not hard operating-system memory/time limits.
A ceiling returns `UNKNOWN`, not an unknot verdict.

The Python API supports an uncapped algorithm:

```python
from unknot_windows import Diagram, low_window, probe, adaptive_probe

d = Diagram.from_braid(3, [1, 2] * 4)
ranks = low_window(d, 2).ranks   # unshifted homological degrees <= 2
partial = probe(d, 0)           # UNKNOWN when unseen degrees remain
exact = adaptive_probe(d)      # complete with no caps; can be exponential
```

The package uses the audited upstream PD conventions. Derive crossing signs
from the validated PD traversal, **not** from the signs of the input braid-word
integers. See the article's convention regression.

## Artifact map

- `unknot_windows/`: controller, certificates, readable source-derived scanner,
  dotted algebra, validated diagrams, independent cube oracle, CLI.
- `tests/`: 14 test methods, including exhaustive small local-algebra checks,
  random cube comparisons, pivot-profile checks, and halo/cap regressions.
- `experiments/`: reproducible paired benchmark and separately counted audit.
- `results/`: raw CSV, JSON inputs and outputs, summarized timings, test logs,
  and the generated LaTeX table. No wall-time assertion is used as a unit test.
- `integration/`: optional adapter and upstream integration checklist.
- `article/`: manuscript TeX/PDF and build script.
- `SOURCES.json`: inspected source blobs, primary papers, and attribution.
- `MANIFEST.sha256`: checksums of the delivered files, excluding the manifest.

## Validation and performance scope

The separately counted audit checks **393 windows on 100 diagrams**, **1,772
nice-order stages**, and **15 padding cases**, with zero failures in the
recorded run. The cube oracle is independent of the scanner's dotted-cobordism
composition. These tests do not constitute a formal proof or a full production
integration test.

The six-input benchmark uses the same supplied readable scanner in both modes,
with identical crossing order and min-fill policy. On the 14-crossing weaving
input, full homology took a median 3.6212 seconds and the depth-two low window
0.03784 seconds; the median of paired ratios was 96.1. Peak pre-cancellation
object counts were 5,046 versus 462. These are **backend-only** measurements,
not speedups over the production Python or Rust recognizer. Many benchmark
inputs may be rejected earlier by production polynomial filters.

The adverse controls are preserved: a two-sided probe was slower than full
homology on the torus case, and the padded unknot probe returned `UNKNOWN`.

## Upstream integration status

The upstream source was read through the GitHub connector. A complete upstream
checkout was not available for execution. Consequently the optional adapter is
**prepared but not upstream-tested**. The actual current Python and Rust test
suites were not run here. Nothing has been pushed to GitHub or enabled by
default. The archive is intended for a separate experimental subdirectory,
for example:

```
Topology/UnknotRecognition/research/extremal-windows-20261007/
```

Read `integration/README.md` before connecting the controller to the upstream
backend. No third-party paper PDF or entire upstream source tree is bundled.

## Build article

```bash
sh article/build.sh
```

This requires a conventional TeX installation with pdfLaTeX, Latin Modern,
AMS packages, microtype, listings, booktabs, and hyperref. No bibliography
processor is needed. Regenerating benchmarks rewrites the included table;
rerun the article build afterward. Exact timings in the narrative describe the
shipped run and should be updated before publishing a newly measured edition.

## Mathematical status

Written proofs are provided, but have not been independently peer reviewed or
formalized. The binomial object-count theorem is attributed to
Kelomäki–Schütz; local cancellation follows Bar-Natan; positive unknot detection
ultimately uses Kronheimer–Mrowka. The openai/math categorical manuscript is a
structural comparison only, not a dependency for the results proved here.
