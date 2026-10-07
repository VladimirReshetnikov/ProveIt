# Reproducing the research continuation

Run the commands from the extracted `unknot_structural_compression` directory
unless a command explicitly changes directory. The code requires Python 3.10+;
the recorded run used CPython 3.12.14 on Linux. No Python dependency is required
for recognition, certificate verification, tests, or benchmark measurements.

## Verify the supplied bytes

```bash
python3 scripts/verify_archive.py
```

This checks the final SHA-256 inventory and, independently, the size, SHA-256,
and Git blob identifier of each pinned reference file. Generated rerun outputs
are not required by the inventory. The manifest excludes itself to avoid a
self-referential digest.

## Run the complete suite

```bash
cd fast
python3 -m unittest discover -s tests -v
cd ..
```

The delivered validation log records **69 tests, all passing**. Timing of a test
suite is not a performance benchmark; it varies with host load. The suite includes
the generic set-algebra and independent-cube comparisons from the baseline and
new structural, sharing, Euler, and integration checks.

The standalone symbolic-family checker is separate:

```bash
python3 benchmarks/defect_one_family.py --max-k 100
```

It reports 99 checked diagrams, ending at 202 crossings. Run this checker without
Python's `-O` flag: its internal assertions are part of the verification.

## Exercise each backend

The following commands intentionally bypass all earlier certificate/filter stages
so that the selected backend performs the decision:

```bash
cd fast
python3 -m fastunknot recognize examples/conway_sum_2.json \
  --no-seifert --no-reduction --no-descending --no-factor \
  --no-alexander --no-jones --backend shared
python3 -m fastunknot recognize examples/conway_sum_2.json \
  --no-seifert --no-reduction --no-descending --no-factor \
  --no-alexander --no-jones --backend saturated
python3 -m fastunknot recognize examples/conway_sum_8.json \
  --no-seifert --no-reduction --no-descending --no-factor \
  --no-alexander --no-jones --backend euler
cd ..
```

The first command returns exact ranks; the second returns final `rank_capped=3`;
the third is expected to return an early `rank_lower_bound_capped=3` at stage 11
of 88. Add `--euler-max-states 1` to the third command to exercise safe inference
exhaustion and completed scanning. A resource ceiling such as `--max-objects 1`
instead returns `UNKNOWN` when the backend needs more space.

The low-level functions are available from their explicit modules:

```python
from fastunknot import Diagram, seifert_certificate, verify_seifert_certificate
from fastunknot.component_scan import (
    compressed_khovanov_rank, compressed_khovanov_decide,
)
from fastunknot.euler_scan import euler_compressed_khovanov_decide

diagram = Diagram.from_braid(3, [1, -2] * 5)
certificate = seifert_certificate(diagram)
assert verify_seifert_certificate(diagram, certificate)
assert certificate["status"] == "KNOTTED"
```

## Benchmarks and exact Euler observations

See `benchmarks/README.md` before rerunning timed experiments. It defines the
measurement boundaries, seeds, rounds, controls, and ratio directions. Repeated
Conway sums test raw scanner compression; they are already easy for the existing
connected-sum recognition stage.

This recorder writes fresh exact Euler evidence without replacing the archive:

```bash
python3 benchmarks/record_euler_examples.py \
  --examples fast/examples --output benchmarks/euler_examples_rerun.json
```

The scientific plot is regenerated from archived observations without running
the recognizer. Matplotlib is required only for this step:

```bash
python3 benchmarks/plot_results.py
```

## Build the article

A TeX Live installation with pdfLaTeX and latexmk is required. The article uses
standard AMS packages, Latin Modern, geometry, microtype, booktabs, tabularx,
enumitem, listings, xurl, hyperref, bookmark, and fancyhdr. The figure PDF is
already supplied; rebuilding the article does not require Matplotlib.

```bash
bash scripts/build_pdf.sh
```

The script compiles from `paper/`, leaves intermediate TeX files under
`paper/build/`, and copies the finished PDF to
`paper/unknot_structural_compression.pdf`. No shell escape or network retrieval
is required. PDF metadata may differ across TeX installations even when the
source and displayed document agree; regenerate `MANIFEST.json` only when
intentionally preparing a new release.

## Recreate and inspect the integration patch

```bash
python3 scripts/make_patch.py
```

This compares the included exact reference with `fast/` and writes a text patch
using the actual repository prefix `Topology/UnknotRecognition/fast/`. Generated
bytecode is excluded. The delivered `provenance/integration_verification.json`
records a successful isolated apply and byte comparison. Applying the patch to
a real repository is a separate, user-controlled operation described in the
main README.

## Interpreting a reproduction

Exact decisions, ranks, formula checks, and deterministic operation counts should
agree. Wall-clock times, bootstrap intervals, and CPU-affinity availability need
not. The optional Euler engine may stop earlier than a full scan; its prefix
statistics do not report the maximum frontier over the unvisited suffix. The
complexity theorem uses the complete planned order.

The finite-type hypothesis has not been established for all knot diagrams.
Passing the tests or reproducing the measurements does not settle that open
mathematical requirement.
