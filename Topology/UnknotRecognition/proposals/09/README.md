# fastunknot 0.2: accelerated exact unknot recognition

This is a working, standard-library-only Python replacement for `fast/fastunknot`
in the supplied `Knots.zip`. It retains a complete Khovanov fallback and adds
bounded exact modular obstructions, faster local algebra, and diagrammatic
connected-sum factorization. **It does not implement Lackenby's general
quasi-polynomial algorithm. The unrestricted worst-case bound remains `2^O(n)`.**

Read **[docs/report.pdf](docs/report.pdf)** for the mathematics, complexity bounds,
experimental methodology, and limitations. Its self-contained source is
[docs/report.tex](docs/report.tex).

## Run immediately

Use Python 3.10 or later, from this directory. No installation or network is needed.

```sh
python -m fastunknot recognize examples/conway.json
python -m fastunknot recognize examples/hard_unknot_8.json
python -m fastunknot khovanov examples/conway.json --check-d2
python -m fastunknot jones examples/conway.json
python -m fastunknot recognize examples/conway.json --max-jones-states 1
```

The final command deliberately caps the Jones filter: it must fall back to exact
homology, not guess an answer. To bypass all polynomial/Jones shortcuts:

```sh
python -m fastunknot recognize examples/conway.json \
  --no-reduction --no-descending --no-alexander --no-jones
```

An optional local installation is `python -m pip install .`; it installs the
`fastunknot` console command. Installing requires setuptools for the build, but
the runtime has no third-party dependencies.

## Input and output

The existing formats are preserved:

```json
{"braid": {"strands": 2, "word": [1, 1, 1]}}
```

Alternatively provide `{"pd": [[a,b,c,d], ...]}`, a bare PD array, a rectangular
diagram `{"rows": [[c0,c1], ...]}`, or `{"x": [...], "o": [...]}`. In a PD row
ports are counterclockwise; slots 0 and 2 are under, slots 1 and 3 are over.
Every edge label occurs exactly twice. `{"pd": []}` means **one** crossing-free
circle, not the empty link. Input must describe one component with a spherical
rotation system; links and virtual diagrams are not supported. A file argument
`-` reads JSON from standard input.

`recognize` returns JSON with status `UNKNOT`, `KNOTTED`, or `UNKNOWN`, the chosen
method, timings, and evidence. Exit 0 is a mathematical verdict, exit 3 is a
resource-limited/inconclusive computation, and exit 2 reports an input/option
error. There is no probability of a false verdict from modular arithmetic:
a differing invariant value is conclusive, while equality is only inconclusive.
All these correctness claims refer to the mathematical algorithms; the software
has been regression-tested, not formally verified.

`khovanov` returns exact **F2 ranks**, including the total unreduced rank, half of
it as the reduced rank, and counts by **unnormalized cube degree**. It does not
return an integral homology decomposition or the quantum grading.

## What changed

The new default pipeline is:

```
R1/R2 reduction -> linear descending test -> modular determinant
-> bounded modular Jones -> full Alexander -> factorwise Khovanov
```

The determinant filter uses sparse arithmetic modulo 1,000,000,007. The Jones
filter evaluates the normalized bracket at A=2 modulo the same prime; it uses
frontier matchings, with at most 8192 live states and 250000 transfers by default.
A Jones cap allows fallback. It never turns a matching residue into an unknot
verdict.

The Khovanov backend now uses a locally updated scan-order heap, cached
cobordism topology and crossing transfers, square-free endomorphism
multiplication, self-inverse F2 units, and sparse-fill cancellation priorities.
Its caches have bounded entry counts and are cleared after each raw scan.

Visible two-edge cuts in the planar diagram expose connected sums. Reduced F2
homology ranks are multiplied and degree counts convolved. These are certified
**diagrammatic cuts**, not a general prime decomposition of the knot. Repeated
identical normalized PD factors are computed once per call. Certificate replay
is available as `fastunknot.factors.replay_factor_certificate`.

The oriented sign calculation also now uses both incoming ports, making writhe
and the new Jones normalization invariant under half-turns of individual PD rows.

## Actual measurements

Same-machine medians of five cache-cleared samples; times exclude interpreter
startup and initial JSON/diagram construction. Full data, including small cases
that became slightly slower, are in `results/benchmark.json`.

| Workload | Original | Accelerated | Ratio |
|---|---:|---:|---:|
| Recognize Conway | 33.96 ms | 0.742 ms | 45.8x |
| Recognize Kinoshita–Terasaka | 38.33 ms | 0.712 ms | 53.9x |
| Recognize T(3,61), 122 crossings | 3.710 s | 7.115 ms | 521.5x |
| Full Conway F2 homology | 34.70 ms | 12.32 ms | 2.82x |
| Full homology, eight trefoil summands | 1.287 s | 1.783 ms | 722.2x |
| Same greedy ordering, 1024-crossing curl family | 3.429 s | 29.11 ms | 117.8x |

The supplied 36-crossing stress braid's raw homology finished in 1.767 s
(1.698 s without factor-search overhead). The baseline reached both the original
8-second comparison cutoff and a separate 60-second single-sample cutoff. These
are **censored runs, not baseline completion times or exact speedup ratios**.
Both pipelines recognize that knot much more quickly using an invariant; raw
homology and recognition are deliberately reported separately.

Thirty-two trefoil summands have unreduced rank 3,706,040,377,703,682. The new
backend computed its degree counts in 5.736 ms, with at most 18 explicitly stored
chain objects in an individual factor scan. This does not say that the original
recognition pipeline needs to compute this rank: its filters already reject
such knots cheaply.

## Proven bounds, and what is not claimed

For a fixed number of starting crossings, the identical greedy ordering policy
now takes O(n log n) rather than O(n^2) word operations. The descending test is
linear rather than quadratic. Jones evaluation has a bound in terms of the
number of frontier matchings; a narrow frontier alone does **not** bound full
Khovanov generator multiplicities.

If detected diagrammatic factors have crossing counts n_1,...,n_k, the full
rank backend runs in `poly(n) + sum_i 2^O(n_i)` time, including polynomial-bit
arithmetic for degree-count convolution. Thus largest factor O(log n) gives a
polynomial bound, and largest factor O(log^2 n) gives a quasi-polynomial bound
**on those restricted input classes**. No such factor-size promise holds for
all knot diagrams, and no general quasi-polynomial guarantee is made.

## Options and resource semantics

`--seconds S` is a **cooperative** global budget, not a hard real-time or OS memory
limit. `--max-objects M` bounds the homology scanner's live objects; it does not
bound morphism terms, total bytes, input conversion, or all caches. A valid early
Jones/determinant certificate may finish without using any homology objects.
`--max-jones-states` and `--max-jones-transitions` affect only the optional filter.

`--no-alexander` disables both full Alexander and its modular determinant
prefilter. `--no-determinant` disables only the latter. `--no-jones` and
`--no-factors` disable the other new stages independently. The Python API accepts
`None` for filter ceilings to remove them. An explicit crossing order supplied
to `khovanov_rank(..., order=...)` disables factorization, so exactly that order
is used. For hard service-level deadlines run the CLI in a separate OS process.

## Reproduce

```sh
PYTHONHASHSEED=0 python -m unittest discover -s tests -v
python tools/benchmark.py --seconds 8 --repetitions 5
python tools/stress_followup.py --seconds 60
python tools/benchmark_tables.py
cd docs
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

There are 47 test methods, including the original 19 (adapted only to retain
old method expectations), independently computed cube-of-resolutions checks,
modular state sums, randomized comparisons with the original scanner, diagram
isotopy checks, limits, CLI behavior, and factor-certificate tampering tests.
`results/test_output.txt` records the executed suite. The large stress rank was
not independently recomputed to completion by the baseline; this is not hidden
by the agreement checks for completed paired runs.

`baseline_fastunknot/` is byte-for-byte original source from `fast/fastunknot/`,
retained for transparent comparisons. It is not installed in the new package.
See `PROVENANCE.md` for the source and artifact map.
