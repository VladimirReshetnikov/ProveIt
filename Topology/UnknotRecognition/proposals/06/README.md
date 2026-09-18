# Accelerated exact unknot recognition

**Start with [the report](docs/report.pdf) or [the package guide](fast/README.md).**
This is a runnable replacement for `fast/` in the supplied `Knots.zip`, with the
original backend retained under `baseline/fast/` for reproducible comparison.

## Main results

The general complete algorithm remains exponential; **no general
quasi-polynomial guarantee is claimed**. The delivered implementation achieves
practical speedups and a restricted asymptotic improvement through visible
connected-sum factorization.

Same-machine, sequential, fresh-process API timings (medians of three runs):

| Calculation | Supplied version | Improved default | Result |
|---|---:|---:|---|
| Conway recognition | 33.94 ms | 1.95 ms | KNOTTED, modular Jones |
| Kinoshita–Terasaka recognition | 42.44 ms | 2.16 ms | KNOTTED, modular Jones |
| 40-crossing random 3-braid rank | 0.621 s | 0.167 s | reduced rank 321 |
| 41-crossing random 4-braid rank | 0.950 s | 0.281 s | reduced rank 109 |
| 36-crossing random 5-braid rank | UNKNOWN at 60 s | 7.885 s | reduced rank 2,949 |
| Eight visible trefoil factors, rank | 1.348 s | 0.002148 s | reduced rank 6,561 |

The 36-crossing case with `tail_crossings=3` finishes in 5.528 s, but uses more
memory; the default is the more conservative two-crossing tail. Its large rank
agrees across three tail choices and a separate simplified-diagram computation,
but was not independently verified by a completed baseline or third-party
homology program. The report records that limitation explicitly.

There are regressions: the supplied hard eight-crossing unknot takes 2.44 ms
in the new full pipeline versus 1.65 ms in the baseline. All ten supplied
pipeline examples and all timed observations are reported, not just wins.
These timings exclude interpreter startup; tiny cases are noisy.

For visible factors of at most `b` crossings, the exact rank backend costs
`poly(n) + n * 2^O(b)`. This is quasi-polynomial for the restricted class
`b=O(log^2 n)`, not for arbitrary prime or hidden-factor diagrams. In particular,
explicit trefoil-sum rank computation becomes polynomial instead of retaining
exponentially many identical boundary objects. The default recognizer already
rejects trefoil sums through Alexander, so that asymptotic comparison concerns
the exact rank backend, not the entire default decision pipeline.

## Quick start

Python 3.10+; no third-party runtime dependencies. Tested on CPython 3.13.5.

```sh
cd fast
python -m fastunknot recognize examples/conway.json
python -m fastunknot khovanov examples/conway.json --check-d2
python -m unittest discover -s tests -v
```

The difficult rank example can also be run directly from `fast/`:

```sh
python -m fastunknot khovanov ../results/stress_input.json --tail-crossings 3
```

The final test run passed **41 methods**, including independent small-cube
comparisons and thousands of algebraic differential checks.

## Reproduce

From the archive root:

```sh
python tools/benchmark.py --repeats 3 --timeout 60
python tools/report_tables.py
python tools/validate_stress.py
sh docs/build.sh
```

The full benchmark takes several minutes and includes an intentionally limited
baseline run. `--select random_5_36` or another substring selects only matching
fixtures. Use `--output results/my_run.json` to preserve the release measurements.
The report tables can be regenerated from `results/benchmarks.json`; narrative
numbers in the report are those of the release run and are not rewritten
automatically. `stress_note.tex` likewise describes the retained release run.

## Layout

`fast/` contains the improved code, examples and tests. `baseline/fast/` is the
untouched supplied baseline, including its older Windows benchmark data.
`docs/` contains LaTeX source, the compiled PDF and supporting table/note files.
`tools/` contains reproducible benchmark and validation scripts. `results/`
contains all current inputs, 146 raw benchmark observations and validation logs.
Only the current same-machine observations support this release's ratios.

All completed recognition verdicts are exact in the mathematical algorithm;
resource exhaustion returns `UNKNOWN`. A modular Jones value of one is never
an unknot verdict. Decomposition certificates certify visible cuts, not all
homology calculations. Neither formal verification nor a full implementation
of Lackenby's hierarchy algorithm is claimed. The article explains both the
improvements and the missing ingredients for a general quasi-polynomial result.

The original permissive license is retained in `LICENSE`; the replacement
package metadata uses its MIT-0 identifier. Original paper and talk PDFs are
not duplicated; their references are in the report.
