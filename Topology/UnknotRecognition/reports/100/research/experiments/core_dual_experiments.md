# Dual forest experiments

The implementation adds `fastunknot/core_dual_forest.py` and an independent
`fastunknot/core_dual_forest_verify.py`. The root integration supplies the
`dual_strategy` option to the existing normal-cut census API. The auxiliary
scripts and source fixtures are provided both with that overlay and here.

## Reproduction

From the patched `Topology/UnknotRecognition/fast` directory:

```bash
python -m unittest tests.test_core_dual_forest -v
python core_dual_matrix_witness.py --output core_dual_matrix_witness.json
python core_dual_benchmark.py --rounds 7 --capacity --output core_dual_paired_timings.json
```

Alternatively, use the scripts in this `experiments` directory with the patched
`fast` directory on `PYTHONPATH`. The benchmark needs Regina; source production
and certificate replay do not. The recorded environment used Regina 7.4.

## Recorded artifacts

- `data/core_dual_unit_tests.log`: all 12 focused tests passed in 1.280 seconds.
- `data/core_dual_extra_audit.json`: an initial independent Regina audit of
  16 source fixtures with interior vertices. All successful censuses agree.
- `data/core_dual_paired_timings.json`: seven randomized timing rounds on
  those 16 fixtures and three additional controls without 3-handles, together
  with A/A ratios, actual source hashes, and two separate binary-capacity runs.
- `data/core_dual_paired_console.jsonl`: the case summaries emitted during
  the paired run, before the separate capacity checks.
- `data/core_dual_matrix_witness.json`: exact source incidence matrices,
  dual forests, maximal-minor permanents, exhaustive positive-pivot searches,
  stopping-set column totals, and the successful geometric core certificate.

The benchmark's `--audit-only` option now includes the three controls as well,
so it produces 19 records; the archived initial extra-fixture audit has 16.
The native source hashes were unchanged from beginning to end of the paired
run. The default strategy was still BFS at measurement time; every measured
call supplies its strategy explicitly.

## Scope of the timing comparison

Native successful timings include certificate construction and independent
source replay. Regina timings include constructing the actual cut,
separating its components, and recognizing each component as a handlebody.
These are whole-cut operations, not whole unknot recognition.

For a source with 3-handles, `disabled` stops at the old conservative refusal.
Its recorded runtime is an abstention cost, not a successful-work speedup
baseline. On the three controls with no 3-handles, all three strategies use
exactly the same census path, so disabled timings can serve as controls.
An explicit/native ratio is recorded only when that native method completes.

## Main observations

Among the 16 interior-vertex fixtures, the disabled path completes none, BFS
completes 11, and maximum-weight selection completes 13. All successful
results independently replay and agree with Regina. The remaining three
cases contain a non-handlebody component in Regina's cut and remain
inconclusive natively.

The additional maximum-weight successes are the five-tetrahedron solid torus
with an interior loop, cut along the empty surface or its boundary vertex
disc. The BFS residual is not merely a failure of a particular greedy order:
for the empty cut, the entire residual row set is a stopping set, with
column totals `(2, 3, 2, 3, 2)`. Maximum-weight deletion removes a different
source 2-handle and admits complete geometric cancellation.

Among the 11 interior-vertex cases completed by both strategies, the ratios
of maximum-weight to BFS median times range from 0.9753 to 1.0386, with median
0.9935. These measurements show no clear runtime benefit from the smaller
raw matrix at these sizes. Coverage improves, and retained raw incidence is
provably minimized for the fixed primal forest.

For 512 times the four-tetrahedron Mobius vector, Regina creates 10,311 cut
tetrahedra from 2,048 normal discs and recognizes 257 solid tori. Native
maximum-weight construction plus replay takes a median 29.18 ms, versus
73.64 ms for Regina; the median paired ratio is 2.497. Regina is faster on
most smaller inputs. These measurements are not an asymptotic proof.

For multiplicity `2^16384`, both native strategies construct and replay the
exact census of `2^16383 + 1` solid tori. The recorded totals are 0.1003 s
(BFS) and 0.1088 s (maximum weight). Each serialized certificate is 5,429,503
bytes. These are single capacity measurements, not paired speedup claims;
no explicit Regina expansion of this input was attempted.
