# fastunknot 0.2.0 — accelerated exact unknot recognition

A runnable improvement of the **`fast/` implementation in the supplied `Knots.zip`**.
It is not a mock hierarchy solver, a timeout-based classifier, or a replacement
of the requested baseline with one of the archive's older implementations.
Python 3.10+ and the standard library are sufficient. Tested here with Python
3.13.5 on Linux; no third-party mathematics package is needed.

**General quasi-polynomial time is not achieved.** The complete, unlimited
algorithm still has an exponential unrestricted worst-case bound. It does have
substantial measured improvements and the parameterized bound

```
poly(n) + n * 2^O(m),
```

where `m` is the largest factor found by the implemented visible connected-sum
decomposition after the initial simplification. In particular, this is
`n^O(log n)` when `m = O(log^2 n)`. This is a restricted-class statement, not a
bound for every diagram. The full reasoning is in `docs/report.pdf` and
`docs/report.tex`.

## Run immediately

From this directory, without installing anything:

```sh
python -m fastunknot recognize examples/conway.json
python -m fastunknot recognize examples/hard_unknot_8.json
python -m fastunknot khovanov examples/random5_36.json --check-d2
python -m fastunknot khovanov examples/conway_sum_12.json --factor
python -m unittest discover -s tests -v
```

An optional installation is `python -m pip install .`; it exposes the
`fastunknot` command. That installation requires setuptools, but running the
source directly does not require pip or a network connection.

The first command gives `KNOTTED` using an exact modular Jones obstruction.
The second gives `UNKNOT`. The third computes **reduced F2 rank 2949** without
preprocessing. The fourth returns **reduced rank 33^12 =
1667889514952984961** as an integer, without constructing that many homology
generators.

## What changed

The categorical scanner now chooses invertible pivots using a sparse
fill estimate rather than last-in-first-out scheduling. It also shares repeated
crossing maps, caches composition with immutable keys, avoids identity
compositions, and uses the fact that every unit in the characteristic-two
square-zero dot algebra is its own inverse. The three persistent caches have
finite entry limits; the crossing-map cache is released after each crossing.

A new scalar frontier dynamic program evaluates a normalized Jones value in a
finite ring. A normalized value different from 1 proves that the knot is nontrivial.
The value **1 is always inconclusive**: it never produces an unknot verdict.
The default filter has state and transition caps and falls back when capped.

A new connected-sum layer finds actual two-edge cuts in the spherical diagram.
Recognition stops on the first nontrivial summand. The optional factored-rank
API multiplies reduced ranks and convolves homological degree counts instead
of constructing a tensor product basis. It also memoizes identical PD leaves.
This is visible diagram factorization, not an oracle for prime decomposition.

The greedy crossing order is unchanged but computed in `O(n log n)` instead
of `O(n^2)` per starting crossing. The descending-basepoint test is linear
instead of quadratic. A crossing-sign bug was also repaired: signs now use
both incoming strands, so rotating a PD row by two slots does not change
writhe. Alexander matrix construction was updated consistently.

## Measured results

Seconds, medians of three **fresh processes**, on the same host. Input parsing,
validation, and imports are outside the timer for both versions. A `>20`
entry is a censored run, not a measured completion time.

| Case and operation | Original `fast/` | New | Ratio |
|---|---:|---:|---:|
| Conway, default recognition | 0.035630 | 0.000915 | 38.9x |
| Kinoshita–Terasaka, default recognition | 0.039297 | 0.000886 | 44.3x |
| 36-crossing example, raw Khovanov scan | >20 | 1.284672 | >15.5x |
| 36-crossing example, default recognition | 0.008082 | 0.005217 | 1.55x |
| Two Conway summands, filters disabled | 1.427456 | 0.010935 | 130.5x |
| Three Conway summands, filters disabled | >20 | 0.012196 | >1639x |
| 1024-crossing chain, **ordering only** | 3.414980 | 0.032857 | 103.9x |

Not every case improves. Default recognition of the eight-crossing hard unknot
went from 0.001621 to 0.001819 seconds; the `T(3,5)` fixture went from 0.000590
to 0.000904 seconds. Extra filters cost time when old filters already suffice.

Do not confuse the 36-crossing raw-scan result with a large full-pipeline
speedup: the old Alexander filter already rejects that example quickly. The
archive's older 600-second timeout was on Windows; it is not the numerator of
any same-machine speedup here. An ablation using the **original uncached
algebra with only the new pivot policy** completed the raw scan in 7.627 seconds
and independently agreed on the rank. Full details and all samples are in
`results/benchmark.json` and `results/summary.md`.

## API and formats

```python
from fastunknot import Diagram, recognize, factorized_khovanov_rank

# A single-component braid closure; PD and rectangular-grid formats also work.
diagram = Diagram.from_braid(3, [1, -2, 1, -2])
result = recognize(diagram, seconds=30, max_objects=200_000)
print(result.status)       # UNKNOT, KNOTTED, or UNKNOWN
print(result.to_json())
```

`Diagram.from_json` accepts `{"pd": [[a,b,c,d], ...]}`, a raw PD list,
`{"braid": {"strands": N, "word": [...]}}`, or the inherited grid format.
PD rows list ports counterclockwise with slots 0 and 2 on the underpassing
strand. See the example files and `diagram.py` for the exact grid conventions.
Validation rejects multiple components and non-spherical rotation systems.
Do not bypass validation by constructing the dataclass directly. The lower-level
`khovanov_rank(pd, ...)` assumes a valid PD diagram.

`recognize` retains the original keyword options and adds `use_jones`,
`use_factorization`, `jones_max_states`, `jones_max_transitions`, and
`pivot_strategy`. CLI counterparts include `--no-jones`, `--no-factor`, and
`--pivot lifo`. To force only the scanner on the original diagram:

```sh
python -m fastunknot khovanov examples/conway.json --check-d2
```

`khovanov --factor` is opt-in; the raw scanner is deliberately still available
for direct comparisons. Returned `by_degree` counts use **raw cube degree**,
not normalized bigrading. No quantum grading or integral torsion is computed.

## Exactness, evidence, and limits

Only sound mathematical tests yield `UNKNOT` or `KNOTTED`. Resource exhaustion
is `UNKNOWN`; a Jones work-cap exhaustion merely skips that optional filter.
`--max-objects` limits the scanner, not independent invariant tests. Thus a
Jones obstruction can decide a knot even with `--max-objects 2`. Time limits
are shared and cooperative, not a hard wall-clock or memory guarantee.

Exit codes: 0 for a completed decision/computation, 3 for a resource-limited
unknown, and 2 for invalid input or a rejected witness.

A standalone Jones witness can be checked on the **same input diagram**:

```sh
python -m fastunknot jones examples/conway.json > conway-witness.json
python -m fastunknot verify-jones examples/conway.json conway-witness.json
```

`replay_decomposition(diagram, cuts)` reconstructs and validates a cut tree.
In a full recognition result, reductions precede cuts and a factor can be
reduced again: replay those traces before checking the respective witness.
The package does not supply a complete independent verifier for every pipeline
result. Jones verification recomputes the evaluation and is not a succinct
polynomial-time certificate checker. Khovanov results are computation evidence,
not formal proofs or spanning disks.

## Reproduce the experiments and paper

```sh
python tools/benchmark.py --repeats 3 --cap 20
python tools/summarize_results.py
python -m unittest discover -s tests -v
cd docs
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The benchmark takes several minutes because some baseline runs are capped.
`baseline/fastunknot` contains the unchanged comparison code. The ablation
worker and deterministic connected-sum constructors are included. `make test`,
`make benchmark`, and `make report` wrap these commands on systems with Make.
LaTeX is needed only to rebuild the paper; the PDF is already included.

The validation run passed **36 tests**, including the original 19 adapted for
new defaults, independent dense cube and Jones comparisons, algebra identities,
PD invariance, cut replay, resource-limit behavior, and the hard 36-crossing
rank with `d^2=0` checks. Two further independent dense computations confirm
rank 33 for both named eleven-crossing examples. Test output and the latter
results are retained in `results/`.

See `PROVENANCE.md` for source and benchmark provenance and `LICENSE` for the
retained MIT No Attribution terms.
