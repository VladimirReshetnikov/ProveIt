# Algebra verification and reproduction

These scripts use the production module
`implementation/fast/fastunknot/dense_compose.py` and the preserved code in
`baseline/fast`. They resolve both locations relative to their own files;
installation and `PYTHONPATH` configuration are unnecessary. The baseline
is loaded under a separate private package name, so it cannot silently resolve
to the production implementation. No production algorithm is duplicated here.

Use Python 3.10 or later with its standard library, without the `-O` option
(which would disable assertions). The archived measurements used Python
3.12.14 on Linux; their JSON includes the reported environment. Run the
following commands from the extracted bundle's root directory:

```bash
python verification/algebra/test_fast_compose.py
python verification/algebra/referee_fast_compose.py
python verification/algebra/audit_grading.py
python verification/algebra/benchmark_dense.py --max-m 11 --repeats 5
```

All three reproduction scripts that emit JSON default to new files alongside
the scripts: `referee_results_reproduced.json`, `grading_audit_reproduced.json`,
and `dense_benchmarks_reproduced.json`. The archived JSON files are preserved.
Each script accepts `--help`; `--output PATH` selects a different destination.
The grading audit also accepts `--examples PATH`, defaulting to the bundle's
baseline examples.

## What each check establishes

| Script | Scope |
| --- | --- |
| `test_fast_compose.py` | Eleven test methods: exhaustive coefficient pairs in 0–2 variables; 120 seeded dense products through 8 variables; 270 homogeneous products through 9 variables; 700 arbitrary component plans checked by an independently written scalar surface rule; 8,637 coefficient comparisons across all 2,879 **noncrossing** matching triples on frontiers of 0, 2, 4, 6, and 8 points; scanner matrix comparisons before elimination and checks of (d^2=0) before and after elimination; direct transfers and the support-32/support-33 branch boundary. |
| `referee_fast_compose.py` | 2,100 associativity identities sampled from **noncrossing** matching objects, including 405 positive-genus intermediate plans; 8,768 transfer comparisons from actual scan-derived matching pools, including all smoothing directions, closed-circle counts 0/1/2, support 32/33, monotone relabeling, and shape-cache reuse. |
| `audit_grading.py` | A separate quantum-shift shadow on the preserved baseline scanner. It checks the degree equation for every differential term before and after elimination in 23 fixture/order runs. The archived run checks 27,723 entries and 31,674 terms. It does not invoke the new coefficient kernel or infer knot type from grading. |
| `benchmark_dense.py` | Cold composition calls on seeded dense endomorphisms of a matching with 4–11 arcs. It compares baseline, adaptive, and forced-dense coefficient arithmetic and asserts exact equality of the three results. These are synthetic coefficient benchmarks, not full recognition timings. |

The matching enumerations above are not enumerations of all unrestricted
perfect matchings. The general correctness claims rest on the algebraic
proofs; arbitrary-plan tests and categorical checks provide additional
implementation evidence. The scripts do not establish a general
quasi-polynomial recognition bound.

## Seeds

The benchmark uses seed `202610071`, the independent referee uses
`202610070123`, and the grading audit uses `202610073`. Unit tests use these
fixed seeds:

| Test group | Seed |
| --- | --- |
| Dense squarefree products | `2601007` |
| Arbitrary component plans | `2701007` |
| Noncrossing matching triples | `2801007` |
| Homogeneous products | `2901008` |
| Scanner comparisons | `2901007` |
| Direct transfers at actual scan stages | `3001007` |

In the dense benchmark, one generator supplies both coefficients and trial
orders. Use exactly `--max-m 11 --repeats 5` to reproduce the archived input
sequence and trial counts. Changing the repeat count also changes later
coefficient samples because it consumes a different number of random values.

## Timing semantics and archived data

`dense_benchmarks_final.json` is the original five-repeat measurement for each
arc count 4–11. Each trial creates a fresh algebra and matching before timing.
The timed interval is one `compose` call: it includes geometric and coefficient
plan construction and arithmetic, and excludes imports, input generation,
algebra-object construction, matching interning, and explicit `gc.collect()`.
No composition plan is warmed up before that timed call. Method order is
shuffled independently in each repeat using the fixed generator.

Reported times are `perf_counter` elapsed seconds. Each method's median is
taken over its five samples; each speedup is the baseline median divided by
the relevant method's median. It is not the median of five paired ratios.
The JSON retains every sample, memo-entry counts, and adapter branch counts.
Reproduced times will vary with hardware, Python version, and system load;
the exact coefficient results should agree.

`grading_audit.json` is the original structural audit result, including all
fixture/order records and aggregate counts. The empty diagram is interpreted
as one unknot circle, consistently with the recognizer; its grading audit has
no differential terms to check.

The portable copies only change module discovery, output destinations, and
command-line defaults/options. They read the integrated production kernel
directly. Their import paths were smoke-checked after adaptation; the
computational test suites and timed experiments were not rerun merely to
repackage them.
