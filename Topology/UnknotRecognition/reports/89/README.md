# Moment-coded first returns for ProveIt

**Article:** *A One-Scalar-Census Boundary Compiler for Compressed Unknot Hierarchies* (12 October 2026).

The package contains the 20-page article (`article.pdf`, `article.tex`), runnable standard-library code, tests, raw paired measurements, and integration notes. It continues the incoming corner-aware boundary-kernel report, rather than repeating its surgery theorem.

## Main results

A residual boundary path has exactly two labelled terminal occurrences. Their count, sum, square sum, and exact edge count can be packed without carries into one scalar orbit weight. A single weighted census recovers every first-return pair, including shared corners, without long path tracing or repeated coning queries. The labels use O(log p) bits. The article also proves finite-group transport and an active holonomy gate, exact noncommutative refinement/coarsening, and one-time compilation of a finite reservoir of candidate ports.

The abstract compiler has polynomial encoded complexity. The article gives an explicit local quasi-polynomial reservoir-search regime. It does **not** prove general quasi-polynomial unknot recognition, produce new geometric decomposing surfaces, or supply patterned admissibility.

## Run

From this directory, with Python 3.10 or newer (tested here with CPython 3.13.5):

```sh
python tests/test_research.py
python code/demo.py
python code/demo.py --bits 16384
python code/benchmark.py
sh build.sh
```

The test suite completed with **23 tests, zero failures, zero errors**, including **33,253 counted inner cases** plus additional contract assertions. The article records those tests and their limits. The numerical test and benchmark files are the completed runs, not projected results.

`build.sh` requires a LaTeX installation with the ordinary packages listed in `article.tex`. The manuscript uses `results/benchmark_table.tex`, which is included; keep that relative path when compiling. No font files or external paper copies are distributed.

## What was actually executed

The scalar/vector compilers, literal reference, restricted binary block oracle, boundary-source models, coarseners, finite-group lifts, and count-only baseline were executed. The block oracle is exact for unit translations and singleton bridges and rejects unsupported families. Stress cases reach 16,386-bit namespace bounds (16,385-bit physical circle lengths) without point expansion.

The native ProveIt adapter was checked against its inspected interface and exercised with API-contract mocks. **It was not run against a full upstream checkout.** The native smoke-test script is supplied for integration; it has not produced native results in this delivery. The source triangulation / parallelity packet to boundary-query adapter remains to be implemented and authenticated.

The timing results compare complete **interface queries** using the restricted block oracle. They do not measure the native AHT implementation, source triangulation processing, independent native replay, or knot recognition. Both gains from query amortization and cases where scalar packing loses to the vector implementation are retained.

## Layout

`code/` contains the standalone implementation and opt-in native adapter. `tests/` contains the deterministic validation runner. `results/` contains test logs, exact example witnesses, all benchmark samples, and the article table. `INTEGRATION.md` describes source and certificate obligations. `SOURCE_AUDIT.md` records the targeted reading and repository pins. `kernel_schema.json` describes the small derived interface output, not a knot certificate.

Suggested destination: the next available `Topology/UnknotRecognition/reports/<NN>/`, removing this package's single wrapper directory as appropriate. No upstream repository files were modified, no commits were made, and no patches were applied.
