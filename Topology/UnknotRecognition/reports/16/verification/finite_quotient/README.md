# Portable finite-quotient experiments

This directory contains the recorded A5-filter experiment and its replay
artifacts. The production solver and the separate certificate checker are
imported from `../../implementation/fast`; no production modules are duplicated
here. Baseline recognizer, Jones, and Khovanov methods are loaded separately
from `../../baseline/fast`.

All commands below start at the extracted bundle root, `unknot_dense_algebra`.
Paths inside the scripts are resolved relative to the script files, so the
bundle can be moved without editing code. Python 3.10 or newer is required;
there are no additional third-party dependencies.

## Replay every stored certificate

```bash
python -B verification/finite_quotient/replay_certificates.py
```

This checks all five fixture hashes recorded in the original benchmark and
replays all ten explicit nonabelian A5 witnesses with the independent checker.
It performs no search and no performance benchmark. Replay of just the Conway
witness is:

```bash
python -B verification/finite_quotient/replay_certificates.py --name conway
```

The checker verifies the input binding, even permutations, equality along the
over-strand, every oriented Wirtinger relation, and an explicit noncommuting
pair. A valid witness proves knottedness. A stored negative search result is
not a certificate of the unknot.

## Check relocated imports without rerunning benchmarks

```bash
python -B verification/finite_quotient/benchmark_finite_quotient.py --smoke
```

This imports both bundled packages, verifies all five recorded fixture hashes,
and replays the Conway certificate. The baseline package is loaded under a
separate Python package name, so its invariant routines cannot accidentally
be replaced by the modified package. Production and baseline diagrams are
constructed separately from the same fixture data.

## Reproduce the experiment

```bash
python -B verification/finite_quotient/benchmark_finite_quotient.py \
  --repeats 9 --include-csp \
  --output verification/finite_quotient/finite_quotient_benchmark_rerun.json
```

The default output is also a new `_rerun.json` file; the original recorded
`finite_quotient_benchmark.json` is preserved. Optional `--implementation-root`,
`--baseline-root`, and `--fixtures` arguments support other checkouts, but are
unnecessary within the complete bundle.

The five fixtures are Conway, Kinoshita–Terasaka, the hard 8-crossing unknot,
T(3,5), and the 36-crossing stress braid. The script runs one warm-up followed
by nine timed calls for each selected method. It includes extraction,
seed planning/search or CSP preparation, and independent witness replay.
Imports and fixture JSON parsing are outside the timed interval. The same
procedure compares the original default pipeline, Jones filter, and raw
Khovanov where those computations were recorded.

The original JSON is copied byte for byte from the experiment. Repackaging did
not rerun or replace its timings. New runs naturally produce different wall
times, especially for millisecond-scale tasks in a shared environment.

## Exact measured fixture bytes

`fixtures/` preserves twelve JSON fixture byte streams used for the benchmark,
certificate construction, structural plans, and negative control. Eleven come
from the original repository examples; T(3,7) is the added control. Every `fixture_sha256` in the
recorded benchmark matches the corresponding file here. These measured byte
streams can differ in a final line feed from the canonical Git baseline; JSON
content and normalized diagrams agree. The discrepancy is transport provenance,
not a mathematical or algorithmic change. Preserve these fixture bytes when
repacking or normalizing source files.

`artifact_manifest.json` records hashes for the files in this directory,
including all fixtures, witnesses, and original result JSON files. The global
bundle provenance describes the canonical Git baseline separately.

## Seed plans and negative control

`seed_plans/` contains five structural propagation plans. A plan specifies seed
arcs and then crossings at which the known over-arc and one known under-arc
force the remaining under-arc. These certify an upper bound on the number of
seeds; they do not claim minimality.

The fixture `fixtures/torus_3_7.json` is a nontrivial determinant-one knot with
no nonabelian A5 image. Its saved results are:

- `find_a5_by_seeds_torus_3_7_result.json`: all 231 seed-tuple orbits exhausted.
- `find_a5_certificate_torus_3_7_result.json`: all 182 explored CSP nodes exhausted.

Both results are `INCONCLUSIVE`. To recompute them through the bundled
production CLI, run the following from `implementation/fast`:

```bash
python -B -m fastunknot.finite_quotient \
  ../../verification/finite_quotient/fixtures/torus_3_7.json --solver seeds
python -B -m fastunknot.finite_quotient \
  ../../verification/finite_quotient/fixtures/torus_3_7.json --solver csp
```

The expected exit status is `3`, denoting `INCONCLUSIVE`. No result from palette
exhaustion should be interpreted as a triviality verdict.

## Tests and interpretation

`test_summary.json` preserves the recorded eleven-method finite-quotient test
run. The actual tests live with the implementation. From `implementation/fast`:

```bash
python -B -m unittest discover -s tests -p test_finite_quotient.py -v
```

The test suite compares the solvers against direct permutation enumeration,
checks structural plans and symmetry counts, tests mirrors and changed PD
presentations, tampers with certificates, exercises budgets, cross-checks small
examples against exact Khovanov rank, and includes the T(3,7) negative control.

The recorded measurements support a useful independent obstruction before
expensive fallback. They do not show a universal default-pipeline improvement:
the original Jones filter already rejects Conway and Kinoshita–Terasaka very
quickly. The filter remains optional and bounded. The article and implementation
notes give the precise seed-parameter bounds, Burnside counts, and limitations
of fixed finite targets.

During packaging, a relocation smoke check imported the implementation and
the immutable baseline source snapshot, verified the five recorded fixture
hashes, and replayed all ten certificates successfully. No timings or full
mathematical test runs were repeated for packaging; see `smoke_summary.json`.
