# Accelerated exact unknot recognition

A working, standard-library-only replacement for `fast/fastunknot/` in the
supplied `Knots.zip`. Python 3.10 or later is required. The implementation was
executed under CPython 3.13.5 on Linux; other Python versions were not tested here.

**This is not a quasi-polynomial implementation.** The unrestricted recognizer
is complete and exact, with an exponential worst-case bound. The changes give
measured practical speedups, faster polynomial preprocessing, and a polynomial
algorithm on explicitly decomposable connected sums of bounded-size factors.

## Run

From this directory (installation is optional):

```sh
python -m fastunknot recognize examples/conway.json
python -m fastunknot recognize examples/hard_unknot_8.json
python -m fastunknot recognize examples/baseline_timeout36.json --seconds 30
python -m fastunknot khovanov examples/baseline_timeout36.json --no-factor
python -m fastunknot khovanov examples/conway.json --check-d2
python -m fastunknot jones examples/conway.json
python -m fastunknot decompose examples/conway_sum_12.json
```

`python -m pip install .` also installs the `fastunknot` console command. No
third-party runtime packages or external knot-theory software are required.
The `baseline/` directory is an unmodified copy of the supplied `fast/` Python
implementation, with its tests and examples, retained for reproducibility.
`acceleration.patch` can be applied from the original `Knots/` root with
`git apply acceleration.patch`; it changes only `fast/fastunknot/` source files.
The standalone archive also supplies the new tests, examples, and report.

## Results and their scope

All values below exclude interpreter startup/imports and input validation.
The ordinary examples use medians of three fresh, serial subprocess runs.
Full data and the generated input PD codes are in `results/benchmarks.json`.

| Workload | Original | Accelerated | Interpretation |
|---|---:|---:|---|
| Conway, complete recognition | 0.092830 s | 0.002823 s | 32.9x faster |
| Kinoshita–Terasaka, complete recognition | 0.082476 s | 0.003428 s | 24.1x faster |
| Conway, raw Khovanov scan | 0.086681 s | 0.027837 s | 3.1x faster |
| 36-crossing recorded timeout, raw scan | did not finish in a separate 120 s kernel-budget run | 2.810384 s (one formal trial) | reduced rank 2,949; not a paired 120 s median |
| 1,024-crossing greedy ordering | 8.117443 s | 0.088788 s | 91.4x, one trial |
| 12 visible Conway factors, full rank | first trial hit 5 s wall cap | 0.176065 s, one trial | reduced rank 33^12; peak 246 live objects per scan |

**The 36-crossing example is a hard raw-backend workload, not a hard recognition
instance:** the original complete recognizer already rejects it in 0.014231 s;
the new complete recognizer takes 0.003462 s. Do not compare the 120 s backend
run with the new recognition time. The trefoil recognition microbenchmark is
slightly slower (0.000188 s to 0.000203 s); extra filters have a fixed cost.

`results/independent-large-checks.json` records an independent dense reduced
cube calculation giving rank 33 for both Conway and Kinoshita–Terasaka. It also
records the 36-crossing accelerated scan with `d^2` checks: rank 2,949 in
3.822706 s. The original scanner did not finish the latter case in the attempted
input-order comparison either. We do not claim an independently completed
original-backend calculation of that 36-crossing rank.

## What changed

* Sparse Gaussian cancellations use a lazy Markowitz fill-in score. Units in
  `F2[x1,...,xr]/(xi^2)` are self-inverse, so inversion is a copy, not a geometric
  series. Identity/local-ring shortcuts and bounded, immutable-result morphism
  caches reduce cobordism-composition work.
* Greedy crossing ordering produces the **same order** in `O(n log n)` per start
  instead of `O(n^2)`. Descending-start detection uses cyclic intervals in `O(n)`
  instead of trying every start separately.
* Exact modular Alexander and normalized bracket/Jones evaluations are
  one-sided rejection filters. Equality is always inconclusive. A Jones state
  ceiling skips that filter and continues to the complete backend.
* Visible diagrammatic connected sums are split using the planar dual.
  Reduced homological-rank polynomials are multiplied factorwise instead of
  materializing every homology generator of the sum. Recognition can stop after
  finding one nontrivial factor. This is **not** prime-knot decomposition.
* The public oriented writhe now uses both incoming ports. The original
  one-port signs are retained separately as `relation_signs()` for the original
  Fox/Alexander row convention; that Alexander computation is not reinterpreted.
* Time and object checks are more frequent. They are still cooperative, not an
  operating-system sandbox. Use an external process timeout for a hard deadline.

The paper proves the algebraic transformations, filter safety, rank-product
formula, restricted-family asymptotic improvement, and the limits of the claimed
complexities. Its discussion of Lackenby's talk and July 2026 paper separates
hierarchy iteration bounds from a fully implemented bit-complexity guarantee.

## API and limits

```python
from fastunknot import Diagram, recognize, khovanov_rank

knot = Diagram.from_braid(3, [1, -2, 1, -2])
answer = recognize(knot, seconds=10, max_objects=100_000)
print(answer.status)                 # UNKNOT, KNOTTED, or UNKNOWN
print(answer.to_json())
ranks = khovanov_rank(knot.pd)       # factors visible sums by default
```

Input formats are unchanged: `{"pd": [...]}`, `{"braid": {"strands": m,
"word": [...]}}`, rectangular `{"rows": [...]}`, or `{"x": [...], "o": [...]}`.
PD rows are counterclockwise `[a,b,c,d]`, with `a-c` under and `b-d` over. The
empty PD means one unknotted circle. Links and nonspherical rotation systems
are rejected. Use the validated `Diagram` constructors; the low-level raw
scanner retains the baseline precondition of a valid knot PD.

`by_degree` records **unnormalized cube degree**, with quantum grading forgotten;
it is not the bigraded Jones polynomial or a normalized homological grading.
Supplying an explicit `order=` to `khovanov_rank` disables factorization and uses
that order literally. `factor=False` / `--no-factor` isolates the scan kernel.
`max_objects` bounds each factor's live Khovanov complex, not the returned rank,
not total process memory, and not the number of Jones matching states.

To force the complete fallback in recognition, use `--no-alexander --no-jones`.
`--no-alexander` disables both Alexander stages but **not** Jones.
`--no-modular` only disables the modular Alexander shortcut. Other switches are
`--no-reduction`, `--no-descending`, and `--no-factor`. The Jones filter defaults
to at most 20,000 live matching states. Unlimited recognition (omit resource
limits) is complete; a user-selected budget can return `UNKNOWN` but never a
false knot verdict merely because a budget was exhausted.

Exit codes are 0 for a completed result (either knot verdict), 3 for `UNKNOWN`,
and 2 for invalid input. Jones alone returns `KNOTTED` or `INCONCLUSIVE`.
Traces and numerical evidence aid replay, but are not standalone, formally
verified certificates. No Lean formalization or external certificate checker is
included. Caches are bounded by entry count, not byte count, and concurrent calls
are not promised to be an efficient parallel execution mode.

## Tests and benchmarks

```sh
python -m unittest discover -s tests -v
python -m unittest discover -s baseline/tests -v
python tools/benchmark.py --hard-timeout 12
# Resume an interrupted run, processing two additional cases:
python tools/benchmark.py --resume --max-cases 2
```

The new suite has 30 test groups, including 120 independent dense cube comparisons
(with and without factoring), 50 original/new degree comparisons, 24 scan-stage
`d^2` runs, 500 order/descending comparisons, 360 independent bracket evaluations
in three rings, all 128 units on three arcs, 200 general morphism compositions,
Reidemeister/braid/PD-convention checks, and connected-sum/limit tests. The
preserved original 19 tests also pass. These are strong finite regression checks,
not a proof of implementation correctness on all inputs.

Formal benchmarks are cold and serial. A subprocess timeout includes startup;
reported successful kernel seconds do not. Timeouts are censored observations,
not completed times or grounds for a numerical speedup ratio. The full saved run
used three trials on ordinary cases and on the 256-crossing order benchmark;
large ranks, the 36-crossing raw scan, the 1,024-crossing order, and descending
microbenchmark use one trial (two-factor Conway uses three). `--trials 1` can be
used for a faster exploratory run. `tools/baseline_hard.py` reproduces the
supplementary 120 s baseline observation; run it under an external process limit.

## Paper and licensing

`paper/report.tex` and `paper/report.pdf` contain the mathematical and engineering
report. To regenerate the tables and PDF:

```sh
python tools/report_tables.py
cd paper
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The supplied software license is preserved (`LICENSE`, MIT No Attribution /
MIT-0). The public research papers are cited, not redistributed. This delivery
extends the archive's implementation; it does not attribute the implementation
or its engineering choices to Lackenby or to the cited homology authors.
