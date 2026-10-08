# Exact compression for unknot recognition

This research package contains three proved algorithms, executable implementations, and reproducible experiments for the ProveIt unknot-recognition program. The article is [paper/unknot_exact_compression.pdf](paper/unknot_exact_compression.pdf); its main source is [paper/unknot_exact_compression.tex](paper/unknot_exact_compression.tex).

**The complete recognizer retains an exponential worst-case upper bound.** The package proves a quasi-polynomial bound for prescribed homological queries under explicit diagram parameters. Turning these queries or the improved terminal hierarchy operation into a general quasi-polynomial recognizer requires additional theorems and implementation work identified in the article.

Distribution filename: `unknot_research_20261007.zip`.
The article was completed on 8 October 2026; the archive name records the source-audit date.

## Contributions

| Contribution | Exact result | Implementation status |
|---|---|---|
| Homological windows | Compute any prescribed interval of unreduced Khovanov homology over F2, with pruning before object allocation and exact handling of the adjacent differentials. | Implemented as a query API, a CLI command, and an optional one-sided recognition filter with complete fallback. |
| Finite nilpotent reduction | Contract the constant-term differential by binary linear algebra, then lift the contraction through a radical whose `(w + 1)`st power is zero, where `w` is the frontier size. | Implemented as a separate research backend with optional exact checks of the deformation-retraction identities. |
| Terminal boundary patterns | Decide essentiality of a trivalent boundary pattern on a known 3-ball in deterministic `O(S log(S + 2))` word-RAM operations, where `S` is the number of darts, with independently checked negative witnesses. | Implemented as a standalone hierarchy subroutine and report appendix. The caller must already know that the ambient manifold is a 3-ball. |

For a diagram with `n` crossings, maximum scan frontier `w`, `s` Seifert circles, minority crossing-sign count `mu`, and requested normalized radius `d`, the article proves the window bound

```text
2^O(w + s + mu + d) (n + 1)^O(mu + d + 1).
```

It is `n^O(log n)` when `w + s = O(log^2 n)` and `mu + d = O(log n)`. This theorem concerns the requested homological groups. An agreeing partial window can leave a nontrivial knot undecided.

## Source baseline and integration

The active Python baseline is `Topology/UnknotRecognition/fast`, version `0.2.0`, at ProveIt revision

```text
ca61a1a5f967999d778d6efd7c882e77a2eb379d
```

That revision also contains a structural-compression continuation in `reports/07`. Its patch had not been applied to the active `fast/` tree. This package targets the active tree directly and does not assume the report-07 patch is installed.

The archive includes a complete working `fast/` tree and the repository-relative patch `integration/fast-window.patch`. Read [INTEGRATION.md](INTEGRATION.md) for patch application, API semantics, and the separate placement of the hierarchy bundle. The supplied patch does not create a complete hierarchy engine.

## Verify and reproduce

All commands in this section start at the unpacked package root unless a directory change is shown.

Run the complete verification:

```sh
python verify.py
```

The recorded run used **Python 3.12.14** and passed **64 tests for `fast/` and 10 tests for the hierarchy subroutine**. The logs are [results/fast_tests.txt](results/fast_tests.txt) and [hierarchy/test_results.txt](hierarchy/test_results.txt).

The window tests compare arbitrary requested intervals and crossing orders with full homology, check mirror degree reversal, test both required guard degrees, verify differentials, and exercise pre-allocation ceilings. The perturbation tests check exact contraction identities. The hierarchy tests include all 10,410 dart pairings on two or four cyclically ordered trivalent vertices, comparison of the 5,628 spherical cases with the report-06 checker, rejection of the 4,782 positive-genus cases, and larger generated examples.

Regenerate the measurements:

```sh
python experiments/window_benchmark.py --repeats 7
python experiments/benchmark_perturbation.py --repeats 5
python -m hierarchy.benchmark_patterns
```

These commands replace the corresponding stored benchmark results with measurements from the current machine. The scripts retain individual repetitions and the parameters needed to reconstruct the inputs. Timings from different runs or machines should be compared through the paired protocols and deterministic work counters.

Regenerate the article figures and tables:

```sh
python experiments/make_figures.py
python experiments/make_tables.py
```

Verify the saved contraction maps and terminal witness without rerunning their constructors:

```sh
python experiments/export_certificates.py --verify-existing
```

The HPL example replays an actual four-crossing knot prefix before checking its saved maps. The terminal example uses the independent primal-cut verifier. The JSON files are in `results/certificates/`. Running the same script without `--verify-existing` regenerates them. `verify.py` includes these checks as well as release-file checksums; after intentionally rebuilding or editing files, use `python verify.py --skip-hashes` to run semantic verification against the modified package.

Rebuild the PDF:

```sh
cd paper
latexmk -pdf unknot_exact_compression.tex
```

The core implementations, tests, and benchmark computations use the Python standard library. Figure generation additionally requires Matplotlib. PDF rebuilding requires `latexmk`, a PDFLaTeX installation, Latin Modern fonts, and the packages named in the article preamble, including `lmodern`, `microtype`, `geometry`, AMS packages, `mathtools`, `booktabs`, `longtable`, `enumitem`, `graphicx`, `xcolor`, `tikz`, `fancyhdr`, `listings`, `xurl`, and `hyperref`. The compiled PDF is already included.

## Use the window calculation

From `fast/`, request the Conway example's raw degree six:

```sh
python -m fastunknot window examples/conway.json --lower 6 --upper 6
```

The result contains `by_degree`, `window_rank`, `complete_rank`, the crossing order, and work statistics. `window_rank` is the sum of the requested groups; it is a total homology rank only when `complete_rank` is true. No homology in the temporary guard degrees is reported.

The Python API accepts raw cube degrees:

```python
from fastunknot.diagram import Diagram
from fastunknot.window_scan import khovanov_window
from fastunknot.window_bounds import khovanov_window_auto

diagram = Diagram.from_braid(3, [1, -2, 1, -2])
negative = diagram.signs().count(-1)

# Exact normalized H^0, returned with the original raw degree labels.
direct = khovanov_window(diagram.pd, negative, negative)
automatic = khovanov_window_auto(diagram, negative, negative)
assert direct["by_degree"] == automatic["by_degree"]
```

Normalized homological degree is the raw degree minus `diagram.signs().count(-1)`. Use this method rather than inferring crossing signs from the signs of braid generator integers. Automatic mirroring minimizes a proved object bound and restores the original raw degree labels in the result. It is not a predictor of actual pivot cost.

Enable the optional recognition stage with:

```sh
python -m fastunknot recognize examples/conway.json --window --window-max-objects 10000
```

The existing reductions and inexpensive obstructions retain their places in the pipeline. The window runs only if the preceding stages are inconclusive. `--window-radius d` requests normalized degrees `[-d, d]`; the default radius is zero. `--window-seconds` limits the optional attempt, and `--window-no-mirror` retains the input orientation. The option is disabled by default.

The unknot has unreduced F2 homology of dimension two in normalized degree zero and zero in every other homological degree. A computed window that disagrees supplies a knot certificate. Agreement invokes the complete scanner. A window-specific resource limit skips the optional stage; exhaustion of the complete recognizer's resources yields `UNKNOWN`.

## Measured outcomes and their limits

On the supplied 36-crossing mixed five-braid example, the exact normalized-zero-degree window has dimension **698**. The peak allocation falls from **17,694 to 7,692 objects**. Under an identical **10,000-object ceiling**, the full scan stops while the window completes with a nontriviality certificate. Seven warmed alternating timing pairs give medians of approximately **0.904 seconds for the full scan and 0.582 seconds for the window**, a ratio of about **1.55** in the recorded environment. See [results/window_benchmark.json](results/window_benchmark.json).

The small Conway and Kinoshita–Terasaka examples also have certifying normalized-zero-degree windows, both dimension ten. Their peak reductions are substantial, while the small timing differences do not establish a broad speed advantage. The recorded mirrored Kinoshita–Terasaka calculation is slower than its full-scan comparison. Torus examples serve as representation controls; earlier filters already decide them.

The perturbation backend is **slower on all five natural knot-diagram measurements**, by approximately **1.17 to 2.27 times**. It remains an explicit research alternative. On the separate algebraic stress complex with a `256 x 256` differential `I + xR`, its recorded median is about **6.48 times faster** than scalar cancellation. Those stress complexes are algebraic inputs, not knot diagrams. These two results have different scopes; both are recorded in [results/perturbation_benchmarks.json](results/perturbation_benchmarks.json).

The hierarchy measurements compare the full terminal classifier, including validation, with the preserved report-06 checker. The new near-linear bound is for this known-ball terminal operation. It does not supply the surface search, compressed cutting, hierarchy construction, or global restart bounds needed by a complete hierarchy recognizer. See [hierarchy/README.md](hierarchy/README.md) and [hierarchy/benchmark_results.json](hierarchy/benchmark_results.json).

## Package layout

| Path | Contents |
|---|---|
| `paper/` | Main LaTeX article, component proofs, references, and compiled PDF. |
| `fast/` | Complete active-baseline Python recognizer with the new optional window stage, query APIs, perturbation backend, examples, and tests. |
| `hierarchy/` | Standalone terminal-pattern classifier, independent negative verifier, fixtures, preserved comparison sources, tests, and report appendices. |
| `experiments/` | Reproduction scripts for measurements, figures, and tables. |
| `results/` | Full Python test log and paired window/perturbation measurements. |
| `integration/fast-window.patch` | Patch targeting the pinned active ProveIt `fast/` tree. |
| `verify.py` | Complete archive verification entry point. |
| `provenance/` | Pinned source hashes, patch-application verification, and primary-source records. |
| `SHA256SUMS` | Checksums of the released files. |
| `INTEGRATION.md` | Repository integration instructions and operational contracts. |

The article separates established mathematical inputs, results proved for this implementation, empirical performance, and open questions. Its final research program focuses on witness completeness, basis changes that improve structural compression, bounded geometric continuations, and the missing compressed hierarchy operations.
