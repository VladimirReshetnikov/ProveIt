# Accelerated exact unknot recognition

An improved version of the Python implementation supplied in `Knots.zip/fast/`.
The complete recognizer remains exponential in the worst case. **No
quasi-polynomial bound is claimed.** The new version preserves exact decisions
and the original input formats, adds sound one-sided filters, and accelerates
the Khovanov backend itself. Python 3.10+; no third-party runtime dependencies.

## Run

From this directory:

```console
python -m fastunknot recognize examples/conway.json
python -m fastunknot khovanov tools/hard36.json --seconds 30
python -m fastunknot recognize examples/hard_unknot_8.json --check-d2
python -m unittest discover -s tests -v
```

An optional installation provides the `fastunknot` command:

```console
python -m pip install .
fastunknot recognize examples/trefoil.json
```

JSON input can be a PD array, `{"pd": [...]}`, a closed braid such as
`{"braid":{"strands":2,"word":[1,1,1]}}`, or either of the original grid formats.
The original diagram validator rejects links, malformed incidence data, and
non-spherical rotation systems. An empty PD represents a single unknot, not an
empty link. Standard input is accepted by using `-` in place of a filename.

```python
from fastunknot import Diagram, recognize

diagram = Diagram.from_braid(2, [1, 1, 1])
result = recognize(diagram, seconds=30, max_objects=100_000)
assert result.status == "KNOTTED"
print(result.to_json())
```

`UNKNOT` and `KNOTTED` are completed decisions. `UNKNOWN` is a resource limit.
A matching modular residue **never** produces an `UNKNOT` decision. The exact
fallback is still run whenever earlier stages are inconclusive.

## Measured results

Same host and Python 3.13.5, three cold-cache repetitions, median timed call;
imports and input construction excluded. Full raw data, including regressions,
are in `results/benchmark.json`. The untouched baseline is included.

| Task | Original | Optimized | Speedup |
|---|---:|---:|---:|
| Raw Khovanov, supplied random 5-braid with 36 crossings | >30 s | 2.233 s | >13.4× |
| Conway, complete recognition pipeline | 47.693 ms | 1.622 ms | 29.4× |
| Kinoshita–Terasaka, complete pipeline | 48.491 ms | 1.004 ms | 48.3× |
| Supplied 40-crossing unknot, complete pipeline | 7.050 ms | 0.404 ms | 17.5× |
| Scan ordering, 2,048-crossing stabilized unknot | 20.202 s | 0.0531 s | 380× |
| R1/R2 cleanup, same 2,048-crossing input | 25.057 s | 0.0138 s | 1,818× |

The 36-crossing rank is **2,949 reduced / 5,898 unreduced**. The automatic and
natural scan orders agree in every cube degree, with intermediate `d²=0`
checks. Those debug runs are separate from the timing benchmark. Other attempted
orders did not finish within external run limits; see
`results/additional-order-notes.txt`. Scan order remains important.

Not every case is faster: the full table retains a raw T(3,5) slowdown and
several small pipeline regressions. The historical 600-second timeout in the
original Windows benchmark is *not* used to calculate our speedup. Timings
were obtained in a shared container and are not an asymptotic complexity proof.

## Implemented changes

- Incremental R1/R2 simplification using permanent darts, local candidate heaps,
  and a Fenwick tree for replayable trace indices: O(n log n) word operations.
  Descending-diagram detection uses circular interval coverage in O(n).
- Incremental greedy scan ordering: O(n log n) per fixed start, retaining the
  exact original score and tie-breaking. The production `tries=12` policy uses
  a constant number of sampled starts (at most 23 because the inherited policy
  is approximate). `tries=None` still tries all starts and costs O(n² log n).
- Sparse modular determinant and capped modular Jones-bracket prefilters over
  a fixed prime. Both can reject, never certify an unknot. The bracket detects
  the supplied Conway and Kinoshita–Terasaka examples even though their Alexander
  polynomials are 1. Its engine is independent of the cobordism implementation.
- Khovanov composition topology and repeated crossing images are cached.
  Every unit in F₂[x₁,…,xₖ]/(x₁²,…,xₖ²) is self-inverse; endomorphism products
  and identities have specialized exact paths. Lazy Markowitz pivot selection
  reduces Gaussian fill, and shared half-compositions avoid repeated work.

The homology representation still retains individual chain objects and their
multiplicities. Small boundary width alone does **not** prove a small complex.
The paper explains the constant-width connected-sum obstruction, correctness
arguments, and the gap between this implementation and Lackenby's hierarchy
approach.

## Controls and compatibility

```console
python -m fastunknot recognize INPUT.json --seconds 30 --max-objects 100000
python -m fastunknot recognize INPUT.json --no-filters
python -m fastunknot recognize INPUT.json --no-filters --no-alexander
python -m fastunknot khovanov INPUT.json --check-d2
python -m fastunknot jones INPUT.json
```

`--no-filters` disables the two new modular stages, while preserving core speedups.
`--no-alexander` disables only the **full symbolic** Alexander calculation; the
modular determinant is a separate filter. The `khovanov` command bypasses all
preprocessing. `jones` reports only a one-sided comparison, not an unknot test.
`--no-reduction` and `--no-descending` retain their original meanings.

The Jones defaults are 50,000 live states and 1,000,000 state transitions.
`--jones-max-states` and `--jones-max-transitions` change them. Reaching these
caps skips the bracket and continues. A global time limit instead returns
`UNKNOWN`. `max_objects` limits only the homology backend, so an earlier filter
may give a verdict even when that ceiling is very small.

Time checks are cooperative, not hard real-time guarantees. Individual Python
operations and the inherited polynomial calculation can overshoot. Object
counts are not byte or morphism-term limits. Four caches have bounded entry
counts but not bounded payload bytes; they are cleared across rank calls.
Use a supervised process with OS resource limits for untrusted large jobs.
Concurrent rank calls share cache state and can disturb performance statistics.

Explicit rank orders must now be permutations of all crossings. The original
unchecked-order path could silently omit crossings; it is rejected. The
`compositions` diagnostic now counts actual calls, so do not compare that
counter numerically with the baseline's different convention. Total rank,
cube-degree ranks, live objects, and boundary sizes retain their meanings.

Recognition exit codes: 0 for either completed exact verdict, 2 for bad input or
options, 3 for a resource limit. Read the JSON status to distinguish knot/unknot.
Raw `jones` exit code 0 means an evaluation completed, not that a knot was decided.

## Reproduce

```console
python -m unittest discover -s tests -v
python tools/benchmark.py --limit 30 --repeats 3
python tools/benchmark.py --only scan-23 --limit 30 --repeats 3 --output results/hard-rerun.json
python tools/verify_hard_case.py
python tools/build_report.py
```

The last command requires `pdflatex`, regenerates tables from measurements,
and writes `docs/report.tex` and `docs/report.pdf`. The generated `.tex` is
standalone. The report template is also included. Rebuilding the paper expects
the complete benchmark, not a subset saved over `results/benchmark.json`.

There are 37 passing tests, including all 168 one-component three-strand braid
words of lengths 2 and 4, independent dense-cube comparisons, randomized
algebra and preprocessing differential tests, normalization checks, and budget
and order validation. The legacy 19-test suite is preserved with documented
method-route compatibility adjustments. `baseline/tests/test_fastunknot.py`
is an unchanged copy of the original suite and can be run separately:

```console
cd baseline
python -m unittest discover -s tests -v
```

## Contents

`docs/report.pdf` and `docs/report.tex` are the technical paper.
`fastunknot/` is the solution; `baseline/` holds the untouched source and tests.
`tools/corpus.json` freezes all 45 measurement jobs, including all 25 raw scans
and all 10 pipeline examples in the supplied benchmark. `tools/hard36.json`
is the difficult input by itself. `results/` contains timings and validation
logs. `docs/changes.patch` is a source patch relative to the original `fast/`
directory. `PROVENANCE.json` and `MANIFEST.sha256` record input and output hashes.

The license is MIT No Attribution (MIT-0), retained from the supplied archive.
No third-party papers or font files are redistributed in this package.
