# Integration into ProveIt

The archive is `unknot_research_20261007.zip`. Its complete report is [paper/unknot_exact_compression.pdf](paper/unknot_exact_compression.pdf), built from [paper/unknot_exact_compression.tex](paper/unknot_exact_compression.tex).

This document describes commands for an integrator's checkout. The research package does not apply a patch to a remote repository.

## Baseline and patch scope

The patch `integration/fast-window.patch` targets paths relative to the **ProveIt repository root**, beginning with `Topology/UnknotRecognition/fast/`.

Its baseline is the active `fastunknot` **0.2.0** tree at commit:

```text
ca61a1a5f967999d778d6efd7c882e77a2eb379d
```

The `reports/07` structural-compression continuation is present at that revision, but its patch was not applied to the active `fast/` code. The delivered patch is based on that active code. A checkout that has separately installed the report-07 patch needs an explicit compatibility review.

The active-tree changes introduce:

- `fastunknot/window_scan.py`: exact requested homological groups with pruning before allocation;
- `fastunknot/window_bounds.py`: a proved object-bound calculation and optional mirror selection;
- `fastunknot/perturbation.py`: a separate finite-perturbation minimalization backend;
- the opt-in window stage in `fastunknot/recognize.py`;
- the `window` command and recognition flags in `fastunknot/__main__.py`;
- semantic window tests, integration tests, and perturbation tests.

The complete fallback and existing default recognition policy remain available. `use_window` defaults to false, and the perturbation backend is selected explicitly through its separate API.

## Apply and verify

First verify the unpacked archive from its own root:

```sh
python verify.py
```

Then, from the ProveIt repository root, inspect the checkout and check the patch against it. Replace the archive path below with its actual location:

```sh
git rev-parse HEAD
git status --short
git apply --check /absolute/path/to/unknot_research_20261007/integration/fast-window.patch
```

After the preflight succeeds, the application command is:

```sh
git apply /absolute/path/to/unknot_research_20261007/integration/fast-window.patch
```

A failed preflight means that the checkout and patch need to be reconciled before application. In particular, preserve any intervening scanner changes and rerun the semantic tests after adapting the implementation.

Verify the integrated active tree:

```sh
cd Topology/UnknotRecognition/fast
python -m unittest discover -s tests -v
```

The recorded package run passed **64 active-tree tests in Python 3.12.14**. The separate hierarchy bundle passed **10 tests**. The exact logs are `results/fast_tests.txt` and `hierarchy/test_results.txt` in the archive.

## Preserve the report and standalone hierarchy bundle

Place the article, experiment scripts, stored results, and `hierarchy/` package under a chosen new report folder in `Topology/UnknotRecognition/reports/`, preserving the bundle's relative paths. Keeping the complete unpacked package there preserves the independent reproduction commands and the exact source/measurement pairing.

The hierarchy code is a standalone terminal subroutine and report appendix. It is not wired into the active recognizer by `fast-window.patch`. Retain the complete `hierarchy/` directory, including `baseline_report06/`, examples, fixtures, tests, and benchmark scripts.

Its API accepts a trivalent boundary pattern on an ambient manifold **already known to be a 3-ball**:

```python
from hierarchy.ball_patterns import classify_pattern, verify_violating_witness
from hierarchy.fixtures import bipyramid

raw = bipyramid(3)
result = classify_pattern(raw)
assert result["status"] == "violating"
assert verify_violating_witness(raw, result["witness"])
```

The `ambient` field records a caller precondition. It does not prove that a manifold is a ball. The module does not construct a hierarchy, cut a normal surface, transport a terminal disc through previous cuts, or decide unknot recognition by itself. Its independently checked negative witnesses and near-linear pattern algorithm can be incorporated into a future hierarchy implementation with those contracts made explicit.

## Window API contract

Run Python examples with the integrated `fast/` directory on the import path, or from that directory.

```python
from fastunknot.window_scan import khovanov_window

result = khovanov_window(
    diagram.pd,
    lower,
    upper,
    order=None,
    max_objects=None,
    seconds=None,
    check_d_squared=False,
)
```

The input is a validated one-component classical PD diagram. The ordinary CLI validates its input through `Diagram`; direct low-level calls follow the existing scanner's validated-input convention.

`lower` and `upper` specify **raw cube degrees**. The result contains exact nonzero `by_degree` entries only within that interval. `window_rank` is their sum. `complete_rank` is true when the interval covers the entire possible raw support. A partial result must not be passed to code expecting `khovanov_rank`'s total `rank` or `reduced_rank` fields.

The normalized degree corresponding to raw degree `h` is:

```python
h - diagram.signs().count(-1)
```

For normalized degrees `[-d, d]`, query the raw interval `[negative - d, negative + d]`, where `negative = diagram.signs().count(-1)`. The signs of braid generator integers are not a substitute for the diagram method. In this baseline, `Diagram.from_braid(2, [1]).signs()` is `[-1]`.

The optional automatic wrapper is:

```python
from fastunknot.window_bounds import khovanov_window_auto

result = khovanov_window_auto(diagram, lower, upper, max_objects=10000)
```

It chooses between the original diagram and its mirror by comparing exact proved object upper bounds. If it mirrors an `n`-crossing diagram, it computes `[n - upper, n - lower]` and then restores returned degree labels with `h -> n - h`. `by_degree`, `raw_lower`, and `raw_upper` therefore refer to the original input. The diagnostic `profile_degree_convention` identifies the orientation used for internal stage profiles. Bound minimization does not guarantee faster pivot behavior.

The moving support band has one guard degree on each side after accounting for all possible suffix shifts. Nonisolated guards must be retained for the incident differentials. The implementation omits them from the requested final ranks and discards an isolated guard only when its entire future degree support misses the target.

## Recognition options and fallback

The new Python options are:

| Option | Default | Meaning |
|---|---|---|
| `use_window` | `False` | Enable the optional one-sided obstruction. |
| `window_radius` | `0` | Query normalized degrees `[-radius, radius]`. |
| `window_mirror` | `True` | Use the proved-bound mirror choice. |
| `window_max_objects` | `None` | Separate ceiling for retained window allocations; otherwise inherit `max_objects`. |
| `window_seconds` | `None` | Separate time allowance for the optional attempt, also bounded by remaining global time. |

The CLI equivalents are `--window`, `--window-radius`, `--window-no-mirror`, `--window-max-objects`, and `--window-seconds`.

The window stage follows the existing inexpensive filters and any enabled Reidemeister-III simplification. It compares the exact normalized result with `{0: 2}`. A difference returns `KNOTTED` with method `khovanov-window-obstruction`. Agreement is recorded as inconclusive and invokes the complete Khovanov scanner. A window-specific `ScanLimit` also invokes that fallback. If the complete computation cannot finish within its resources, the outcome is `UNKNOWN`.

The optional stage is charged against the existing global time budget, including automatic mirror selection. Without a separate `window_seconds` allowance, the window may use the time remaining in that global budget. Set the separate allowance when a bounded preliminary attempt is desired.

The following command isolates the delivered window obstruction on the 36-crossing stress example:

```sh
python -m fastunknot recognize examples/stress_braid5_36.json --window --window-no-mirror --max-objects 10000 --no-reduction --no-descending --no-factor --no-alexander --no-jones
```

The recorded normalized-zero-degree rank is 698 and the retained allocation peak is 7,692 objects. The corresponding full scan reaches a proposed allocation of 17,694 objects and exceeds that same ceiling. This is a resource comparison of the scanner kernels with the preceding filters disabled.

## Perturbation backend

Select the research backend explicitly:

```python
from fastunknot.perturbation import khovanov_perturbation

result = khovanov_perturbation(diagram.pd, certificate=True)
```

`certificate=True` checks the exact differential and deformation-retraction identities over the actual matching algebra. The degree-zero contraction and finite perturbation series do not require a canonical-form oracle or an assumed bound on matching multiplicity.

The recorded natural-diagram benchmarks favor the existing scalar backend: the perturbation implementation is approximately 1.17 to 2.27 times slower on all five measured knot inputs. Its approximately 6.48-fold gain on a `256 x 256` `I + xR` stress complex concerns a separate algebraic family. These inputs are not presented as knot diagrams. Keep the backend separate while pursuing the block structure and sparse arithmetic improvements described in the paper.

## Rebuild the research artifacts

From the root of the preserved report bundle:

```sh
python verify.py
python experiments/window_benchmark.py --repeats 7
python experiments/benchmark_perturbation.py --repeats 5
python -m hierarchy.benchmark_patterns
python experiments/make_figures.py
python experiments/make_tables.py
```

Then rebuild the report:

```sh
cd paper
latexmk -pdf unknot_exact_compression.tex
```

Core Python computations use the standard library; the recorded environment is Python 3.12.14. Matplotlib is needed only to regenerate figures. PDF rebuilding needs Latin Modern and the LaTeX packages listed in the preamble. The included PDF permits review without rebuilding.

The proved general recognition upper bound remains exponential. Preserve the distinction between the proved parameterized homological-query bound, the finite algebraic reduction theorem, and the standalone terminal hierarchy bound when integrating descriptions or benchmark summaries into the repository.
