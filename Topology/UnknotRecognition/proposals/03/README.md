# fastunknot 0.2 — accelerated exact unknot recognition

This is a working replacement for `Knots.zip/fast/`, not an implementation of
Lackenby's announced quasi-polynomial algorithm. The unrestricted complete
backend still has a **2^O(n) general worst-case bound**. It is substantially faster
on the measured corpus, and visible connected-sum factorization gives a genuine
exponential-to-polynomial improvement on specific families described below.

## Run

Python **3.10 or later**, standard library only. From this directory:

```console
python -m fastunknot recognize examples/conway.json
python -m fastunknot recognize examples/hard_unknot_8.json --check-d2
python -m fastunknot khovanov examples/random_braid5_36.json --no-factor
python -m fastunknot recognize examples/conway.json --output witness.json
python -m fastunknot verify-jones examples/conway.json witness.json
python -m unittest discover -s tests -v
```

An optional editable install is `python -m pip install -e .`; it adds the
`fastunknot` command. Installation requires setuptools, but runtime calculations
have no third-party dependencies. No network service, native extension, or
precomputed knot lookup table is used.

Inputs retain the original formats: `{"pd": [...]}`, a PD array, a
`{"braid":{"strands":3,"word":[1,-2,1,-2]}}` object, or the original grid
formats. `{"pd":[]}` denotes one crossing-free circle. PD crossing rows are
counterclockwise, with slots 0/2 under and 1/3 over. Classical one-component
spherical diagrams are required; links and virtual diagrams are rejected.

Verdicts are `UNKNOT`, `KNOTTED`, or `UNKNOWN`. A global cooperative budget, such
as `--seconds 10`, or a backend object ceiling, such as `--max-objects 10000`,
can produce `UNKNOWN`; neither is interpreted as a mathematical obstruction.
The time budget is not an operating-system hard deadline. In particular, a long
individual Python integer operation cannot be interrupted by a callback.
Both definitive verdicts exit 0, invalid input or failed witness verification
exits 2, and an exhausted recognition resource budget exits 3.

## What changed

* The scanning backend compiles surface topology once per matching combination
  and uses Python integer bitsets for F2 dot-polynomial coefficients. Stage-local
  caches replace repeated connectivity work. Every unit in the relevant
  characteristic-two endomorphism ring is its own inverse.
* A lazy Markowitz-style pivot scheduler reduces cancellation fill-in.
  `--pivot lifo` is available for ablation. The original greedy crossing orders
  are reproduced exactly using an O(n log n) heap-based construction per start,
  instead of O(n²) full rescoring.
* Exact modular Alexander obstructions precede symbolic Z[t] elimination. A
  capped scalar Jones evaluation rejects additional knots without constructing
  their Khovanov complexes. Modular equality proves nothing and always falls
  through. `--no-modular`, `--no-jones`, and `--no-alexander` control these stages.
* Certified visible two-edge connected-sum cuts are evaluated by products and
  homological-degree convolution. This is not topological prime decomposition.
  `--no-factor` disables it. An explicit `khovanov --order '[...]'` also disables
  factorization, so the specified whole-diagram order is actually followed.
* The writhe calculation is made invariant under half-turns of individual PD
  rows, with the Alexander under-strand convention updated consistently. The
  original sign convention and original Alexander matrix compensated each
  other; this is **not** a claim that the old Alexander filter was unsound.

The raw `khovanov` command returns unreduced and reduced total F2 ranks, the
unreduced rank in each **unnormalized cube degree**, and instrumentation. It does
not compute the quantum grading, integer torsion, or grading-normalized groups.
Cube degrees can shift when the input is changed by Reidemeister moves.

## Measured results

See `report/report.pdf` and `results/benchmarks.json` for all measurements,
ranges, failures, and limitations. The recorded run used CPython 3.13.5 on one
Linux host, a fresh process for each sample, and sequential trials. Import and
input-conversion times were excluded; crossing-order construction was included.

| Workload | Unchanged original | New version |
|---|---:|---:|
| Raw 36-crossing five-strand input | Did not finish its 60 s budget | 0.897 s median, reduced rank 2,949 |
| Raw 41-crossing four-strand input | 0.856 s median | 0.167 s median |
| Conway recognition | 35.8 ms median | 1.33 ms median |
| Kinoshita–Terasaka recognition | 38.0 ms median | 1.30 ms median |
| Three Conway summands, recognition | Did not finish its 10 s budget | 4.31 ms median |
| Fifty Conway summands, exact rank | Not attempted | 0.163 s median, rank 33^50 |

The hard raw rank was independently matched by the **original explicit
surface algebra with only its pivot scheduler changed**, in 7.30 s. That
instrumented validator is clearly separated from the unchanged baseline and is
not used as the denominator of the main speedup claim. Four further scans
(original/simplified PD, greedy/natural order) matched the same rank with d²=0
checked after every crossing.

Not every input improves: the default pipeline on the supplied eight-crossing
hard unknot increased from 1.83 ms to 2.56 ms because its extra obstruction
stages were inconclusive. Full tables include this regression.

## Reproduce

```console
python -m unittest discover -s tests -v
python benchmarks/run.py --profile smoke --output results/my-smoke.json
python benchmarks/run.py --profile full --output results/my-full.json
python benchmarks/validate.py --hard --output results/my-validation.json
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

`validate.py` checks the delivered `results/benchmarks.json` and optionally
reruns the four large debug scans. `run.py --resume` continues the same saved
profile after an interrupted run. To regenerate report tables from a new full
run, use `python benchmarks/tables.py --input results/my-full.json` before
recompiling. Rerun LaTeX until cross-reference warnings disappear. Small timings vary by machine; the saved observations are not
performance guarantees.

## Exact family improvement and the width limitation

For k visibly joined copies of the supplied Conway diagram, the Alexander
polynomial is 1 and the reduced F2 rank is 33^k. The original unrestricted
pipeline reaches its explicit-rank backend and must retain exponentially many
final generators. The new pipeline is polynomial on this fixed-block family,
even when the Jones filter is inconclusive, because exact factor ranks and their
degree distributions can be combined without expanding generators.

This does not imply a polynomial or quasi-polynomial algorithm for arbitrary
knots. Boundary width controls matching types, not their homological
multiplicities. Trefoil connected sums already have bounded-width layouts but
rank 3^k. A generic `poly(n) * 2^O(width)` bound for this explicit-complex backend
would therefore be incorrect.

## Layout and license

`fastunknot/` is the optimized implementation. `baseline/fastunknot/` is the
byte-for-byte original source used for measurements. `tests/` contains 34 test
methods, including independent dense-cube and scalar-state-sum checks.
`benchmarks/` contains deterministic input construction, cold-process runners,
independent validation, and table generation. `results/` contains raw evidence
and provenance. `changes.patch` applies the runtime source, packaging metadata, and adapted
original-test changes from inside the original `fast/` directory (`patch -p1`).
The full archive also includes the additional independent tests and benchmarks. `report/` contains the technical article and its sources.

The package carries the supplied **MIT No Attribution (MIT-0)** license; see
`LICENSE`. The research papers referenced by the article are not redistributed.
