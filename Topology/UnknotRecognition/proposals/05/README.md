# Accelerated exact unknot recognition — fastunknot 0.2.0

A tested replacement for the `fast/` implementation in the supplied `Knots.zip`.
**Exact verdicts; exponential general worst case. No general quasi-polynomial
running-time guarantee is claimed.** Python 3.10+, standard library only.

The mathematical and implementation report is
[`docs/unknot_acceleration.pdf`](docs/unknot_acceleration.pdf), with LaTeX source
and generated benchmark tables beside it.

## Run

From this extracted directory (no installation required):

```sh
python -m fastunknot recognize examples/conway.json
python -m fastunknot recognize examples/conway_sum_2.json --output result.json
python -m fastunknot verify examples/conway_sum_2.json result.json
python -m fastunknot khovanov examples/conway.json --check-d2
python -m fastunknot bracket examples/conway.json --integer
python -m unittest discover -s tests -v
```

Optional installation: `python -m pip install .`

To replace the old package in place, replace its `fastunknot/` directory with
this one. Retain any user inputs outside that directory. Existing input formats,
`Diagram`, `recognize`, `khovanov_rank`, and the original commands are retained.
There are additional keyword arguments and evidence fields. Tests or applications
that insist on an old recognition **method name** should allow the new exact
methods as well; a verdict need not reach Khovanov homology anymore.

## Measured results

Medians of three cold-process calls per engine. The original code is preserved
in `reference/baseline_fastunknot/`. Timed calls exclude interpreter startup,
imports, and the initial input parse, but include subsequent internal validation.
All raw trials, inputs, options, minima/maxima, and environment data are in
`results/benchmark.json` and `.csv`.

| Same requested task in each engine | Original | Optimized | Ratio |
|---|---:|---:|---:|
| Recognize Conway | 39.304 ms | 0.822 ms | 47.79× |
| Recognize Kinoshita–Terasaka | 39.313 ms | 1.018 ms | 38.61× |
| Recognize Conway # Conway (22 crossings) | 1399.518 ms | 2.462 ms | 568.54× |
| Raw Khovanov rank, 256-crossing unknot chain | 231.987 ms | 20.751 ms | 11.18× |
| Raw Khovanov rank, 1024-crossing unknot chain | 3601.461 ms | 84.039 ms | 42.85× |

These are sample-specific results, not universal speedups. Full recognition of
the hard eight-crossing unknot regresses from 1.629 to 2.242 ms because the new
filters cannot reject it. Some other small cases also regress. Both raw backends
return UNKNOWN on the selected 36-crossing stress case with the three-second
cooperative budget. The full report contains every benchmark case, including
regressions and resource-limit outcomes.

## Main changes

* Sparse modular Alexander determinant followed by a budgeted modular Kauffman
  bracket. If the completed bracket matches, an exact scaled-integer evaluation
  can avoid finite-field collisions. Only a mismatch proves KNOTTED; equality or
  filter-budget exhaustion is inconclusive and falls through.
* A compiled F2 cobordism kernel: cached topology independent of dot terms,
  component bit masks, square-free endomorphism multiplication, identity
  shortcuts, and the exact identity `(1 + nu)^-1 = 1 + nu` in characteristic two.
  New morphism caches freeze stored values and return separate mutable sets.
* The exact same greedy scan order, computed in O(r n log n), versus O(r n²),
  for r starts. The descending test is O(n), versus O(n²).
* Correct oriented writhe for arbitrary valid PD encodings. The Alexander
  under-arc convention is adjusted consistently, preserving its polynomial.
* Finite LRU entry ceilings, additional deadline checks and input validation,
  and replay/recomputation of modular or integer knottedness evidence.

The full Alexander polynomial and complete Khovanov fallback remain available.
The original LIFO elimination strategy and R1/R2 simplifier are retained.
The package does not contain a knot-name lookup table or unimplemented
hierarchy-algorithm placeholders.

## Input conventions

```json
{"pd": [[1,4,2,5], [3,6,4,1], [5,2,6,3]]}
{"braid": {"strands": 3, "word": [1,-2,1,-2]}}
{"rows": [[0,2], [1,3], [2,4], [0,3], [1,4]]}
```

PD rows are counterclockwise `[a,b,c,d]`, under strand `a-c`, over strand `b-d`.
Every edge occurs twice. One component and a spherical rotation system are
required. `{"pd": []}` means one crossing-free circle. Grid rows are bottom to
top; verticals pass over horizontals. See the report for braid/writhe conventions.

## Budgets and method switches

The recognizer's default **per-evaluation** bracket budget is
`10000 + 200 * reduced_crossings` smoothing transitions and 4096 live states.
A filter limit does not make the whole recognizer UNKNOWN; it skips that filter.

```sh
# Force the complete backend, disabling all preprocessing and invariants.
python -m fastunknot recognize examples/hard_unknot_8.json \
  --no-reduction --no-descending --no-alexander --no-jones --check-d2

# Limit only the expensive backend, while allowing filters to succeed.
python -m fastunknot recognize examples/conway.json --max-objects 1

# Skip bracket work by exhausting its transition allowance immediately.
python -m fastunknot recognize examples/conway.json --jones-max-transitions 0
```

`--no-alexander` disables both modular determinant and full polynomial.
`--no-modular` disables only modular determinant, not the bracket.
`--no-jones` disables both bracket evaluations.
`--no-integer-jones` disables only the exact-integer follow-up.

`--max-objects` applies to the Khovanov backend only. `--seconds` is cooperative,
not a hard process deadline; validation, planning, large scalar operations, and
Reidemeister simplification may overshoot. Use an OS subprocess limit for a hard
wall-clock policy. LRU bounds count entries, not bytes.

Recognition returns exit code 0 for either exact verdict, 2 for invalid input,
and 3 for UNKNOWN. Verification returns 0 when accepted and 4 when rejected.
The `bracket` utility is not a recognizer: its successful exit code is 0 even
when `detected` is false. Inspect `complete` and `detected` in its JSON.

## Verification and experiments

The recorded run passes **42 unittest methods**, including 168 exhaustive small
braid words, independent exact bracket state sums, independent reduced Khovanov
cubes, 2168 basis-composition comparisons, random associativity tests, all units
through three arcs, arbitrary row rotations, mirrors, R3/Markov checks, resource
and tampering checks. Random samples are deterministic and may represent repeated
knot types. This is not a Lean formalization or exhaustive testing of all knots.

`verify` replays the legal R1/R2 trace and recomputes the modular or integer
obstruction on the reduced input. It does not verify arbitrary Khovanov result
JSON. Recomputing a bracket can be expensive; no short-certificate or
polynomial-time-verifier guarantee is claimed. Saved examples are under
`results/witnesses/`.

```sh
python benchmarks/run.py --repeats 3 --seconds 3
python benchmarks/make_tables.py
cd docs
pdflatex -interaction=nonstopmode -halt-on-error unknot_acceleration.tex
pdflatex -interaction=nonstopmode -halt-on-error unknot_acceleration.tex
```

The benchmark uses fresh `python -S` workers for both engines, with hash seed zero.
The original raw backend starts its soft deadline after planning, explaining
why some completed original calls take longer than the nominal three seconds.
The new backend starts its deadline before planning. The parent hard ceiling is
5.5 seconds. Partial/limited trials are never counted as completed recognition.

`tools/families.py` constructs the connected sums used in the tests. The report
proves a family-specific separation: a bounded-width exact bracket scan rejects
all powers of the supplied Conway knot in polynomial bit time, whereas explicitly
materializing their minimal Khovanov complexes requires exponentially many
objects. This is not a general bound for the default greedy recognizer.

## Contents and license

`fastunknot/` is the solution; `tests/` contains the active tests; `reference/`
contains the preserved baseline; `benchmarks/` contains paired measurement tools;
`tools/` contains input constructors; `examples/` contains input fixtures;
`results/` contains raw measurements and validation; `docs/` contains the report;
`dist/` contains a built and smoke-tested pure-Python wheel.

The original MIT No Attribution license is preserved in `LICENSE`. Original
baseline code remains credited to the Knots Contributors. The new modifications
and report are distributed under the same license. The literature itself is not
redistributed; bibliographic references identify the supplied and public sources.
