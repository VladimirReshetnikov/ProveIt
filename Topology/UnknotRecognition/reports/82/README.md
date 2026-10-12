# Corner-aware boundary kernels for compressed unknot hierarchies

Research continuation for `VladimirReshetnikov/ProveIt`, 12 October 2026.
The full article is `article/article.pdf`; its LaTeX source and generated tables are alongside it.

## What this package establishes

A finite interface operator for **abstract marked compact surfaces**, intended for the next stage after ProveIt's source-parallelity construction. With `p` named boundary cells it retains at most `2p` edges and corners. It distinguishes adjacent ports from ports separated by a nonempty path; counts alone cannot make that distinction. It computes exact surface type after disjoint signed pairings, and returns a normalized kernel for later pairings.

The Euler update is

    chi_after = sum(chi_before) + number_of_pairs - (corners_before - corners_after).

The corner correction is necessary for adjacent ports and whole-circle attachments. The compiler obtains ordered boundary information from unweighted orbit-count callbacks in O(p log(p+1)) calls, with an optional third relation for silent interior-corner cancellation. A general polynomial compiler follows from the classical AHT orbit-count theorem when the stated geometric inputs are supplied.

**This package does not provide a general quasi-polynomial unknot recognizer.** It neither changes `recognize` nor certifies that an abstract base gluing is a legal three-dimensional hierarchy move. The native source-to-V/R/F adapter is not included. The optional upstream count wrapper was written against the inspected API but was not executed against the repository. The fibre-holonomy extension theorem is proved in the article, not implemented here.

## Run

Python 3.10+; standard library only. Tested on Python 3.13.5, Linux.

```sh
python verify_artifacts.py  # before regenerating any files
PYTHONPATH=src:tests python -m unittest discover -s tests -v
PYTHONPATH=src python examples/counterexamples.py
PYTHONPATH=src python examples/large_boundary.py
python benchmark.py --output data/benchmark-rerun.json
sh build.sh
```

`build.sh` requires `pdflatex`. On Windows, set `PYTHONPATH` using your shell's syntax, or install the package with `python -m pip install -e .` and make `tests` importable when running the test suite. No registry access is needed to run the source directly with `PYTHONPATH`.

## Results in this delivery

The 18 test methods include 7,688 exhaustive signed partial polygon pairings, 1,600 deterministic randomized surface/composition cases, and 700 randomized compiler cases. Other tests include invalid inputs, cancellation, shared budgets, tampered transcripts, loop edges, silent interior orbits, and 16,385-bit coordinates. See `data/test-output.txt` and `data/validation.json`.

The local timing comparison evaluates the same encoded surface-gluing query by kernel construction plus surgery, and by an independent literal expansion. Seven shuffled paired batched rounds, a warmup, and an identical literal control are retained. Small-input regressions are included. **This is not a native ProveIt or complete knot-recognition speed comparison.** The huge-coordinate compiler timing uses analytic block oracles, not general AHT.

## Contents

- `article/`: complete proofs, implementation contract, measurements, and further research questions.
- `src/corner_kernel/`: exact kernel, compiler, test oracles, bundle consequences, optional upstream adapter.
- `tests/`: exhaustive/randomized tests and independent literal boundary reference.
- `examples/`: runnable topological counterexamples and huge binary boundary example.
- `data/`: all completed test/benchmark evidence; the noisier first timing pass is preserved separately.
- `INTEGRATION.md`: source contract and proposed opt-in integration, including remaining trust boundaries.
- `SOURCE_AUDIT.json`: inspected repository paths/blob IDs and external primary sources.
- `SHA256SUMS`: content hashes for the delivered files.

## Important conventions

Port labels are unique. A gluing uses two distinct port cells; each cell may appear in at most one pairing. Closures may share endpoints, and loop cells are supported. A positive `Edge(length=N)` is an unmarked path; consecutive port edges mean zero gap. Never encode a zero-length gap as an edge.

On an orientable source component, stored boundary-cycle directions must be coherent induced directions, not independently chosen orientations. Port `reverse` bits are relative to those directions. A gluing's `reverse=1` reverses the supplied port parameters. Gap length one produced by the compiler denotes a positive source path, not a claim about its original length.

Component statistics and compressed source relations are inputs requiring independent geometric certification. Transcript recomputation is not proof-only replay of native AHT certificates. The kernel retains topology for future port-only surgery, not arbitrary pattern words or witness-lifting provenance. Port-free repeated source profiles must remain aggregated outside the explicit active-component API.

## Attribution and license

This continuation builds on classical Agol–Hass–Thurston orbit counting, classical surface topology, and ProveIt's existing coning, compressed raw-cut, and all-dimensional parallelity work. Relevant source checkpoint: `ed166080d7db14dd7a91d07788996f02947dd92a`. No exhaustive literature-priority claim is made.

All newly supplied source, article, and data: MIT-0; see `LICENSE`. No third-party manuscripts or repository source files are redistributed in this archive.
