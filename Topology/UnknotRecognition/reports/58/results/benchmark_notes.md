# Paired topology-spectrum benchmark notes

The authoritative measurements are `benchmark-final.json`. They use the byte-exact
inherited source at ProveIt commit
`eb368edf975695e3e16a8774dcb7846bda0c13a0` plus the six delivered runtime modules.
Every recorded source hash agrees before and after the completed experiment.
The separate provisional run made before correction of an inherited terminal-newline
materialization error was interrupted and excluded; it is not part of this evidence.

## Design and completed work

There are 13 supplied-normal-vector cases, four arms, one shuffled warmup round,
and **five shuffled measured rounds per case**, with seed `2026100919`.
All **260 measured arm executions and 52 warmup executions completed**, returned
identical topological spectra for their respective cases, and passed independent
certificate replay. No incomplete sample was excluded from these totals.
The completed run lasted from 04:57:23 to 05:00:26 UTC on 9 October 2026.

The arms are the new direct two-weight query, an identical direct A/A control,
the new query with vertex-link/content reduction, and a reference composition of
existing maintained APIs. The reference runs the full `7t`-coordinate component
census, then calls the connected-surface topology routine on each distinct
component vector, and merges equal homeomorphism types. It computes finer
component embedding data on the way to the same final topological answer.
The old aggregate-only topology summary does not answer this question and is
not used as an equivalent-output timing baseline.

Producer and verifier times are recorded separately with `perf_counter_ns`.
They include source validation, certificate construction and replay, but exclude
fixture construction, certificate JSON serialization and output-file writes.
Each reported speedup is the median of the five within-round ratios, not a ratio
of independently computed medians. Producer, verifier and total medians are each
computed independently, so the first two medians need not sum to the third.

## Representative results

Times below are medians of producer plus verifier time. The comparison column
gives the median paired ratio with the first arm in the numerator.

| Case | First arm | First time | Second arm | Second time | Paired ratio |
|---|---|---:|---|---:|---:|
| 128-tetrahedron meridian | Coordinates reference | 14,912.555 ms | Direct two weights | 2,662.092 ms | 5.7327 |
| 32,779-bit meridian-plus-links input | Direct two weights | 331.892 ms | Reduced two weights | 32.055 ms | 10.3681 |
| Even Möbius-plus-links, 4,097-bit input | Direct two weights | 3.021 ms | Reduced two weights | 0.881 ms | 3.5131 |
| Odd Klein-plus-links, 4,098-bit input | Direct two weights | 7.678 ms | Reduced two weights | 1.553 ms | 4.6724 |

For the 128-tetrahedron meridian, the reference uses 896 coordinate weights and
reaches 385 constant weight runs; the direct query uses two weights and reaches
nine runs. The reference uses four orbit queries and 530 cycles, while direct
uses three queries and 397 cycles. Their canonical JSON certificate sizes are
6,082,406 and 3,579,367 bytes respectively. Separate producer medians are
8,215.269 and 2,484.329 ms; separate verifier medians are 6,767.796 and 177.763 ms.

For `meridian_links_b32768`, the full coordinate gcd is one. Core reduction
changes query-coordinate size from 32,779 bits to 11 bits, cycles from 100 to 61,
and peak constant-run count from 51 to nine. Canonical certificate bytes decrease
from **10,081,806 to 123,278**. The producer medians are 250.077 and 21.514 ms;
the verifier medians are 80.859 and 10.423 ms. Both arms still read and bind the
original large input. The kernel does not remove that input-size cost.

## Negative cases and limitations

The direct two-weight route is **not uniformly faster** than the coordinates
reference. On `meridian_links_b32768`, the reference median is 299.004 ms versus
331.892 ms for direct; its paired reference/direct ratio is 0.8997. On the even
Möbius case that ratio is 0.9453. The reduced route is faster on both cases.
On primitive meridians there is no consistent gain from core reduction. At
32 tetrahedra its median is 93.117 ms versus direct 84.474 ms, with a paired
direct/reduced ratio of 0.9125. All such results are retained in the raw record.

The per-case median A/A total-time ratios range from 0.9155 to 1.0279, showing
that scheduling and machine noise remain visible, particularly on small calls.
Five rounds on fixed constructed families do not constitute a population study.
No statistical confidence claim or fitted asymptotic exponent is asserted.

These are normal-surface subroutine measurements. They do not time whole-knot
recognition, normal-vector discovery, a complete hierarchy, or Regina. The
two-weight dimension, run counts and serialized certificate sizes are measured
structural quantities; **peak resident memory was not measured**. A smaller
serialized proof or fewer weight runs must not be reported as a measured RAM
reduction. The benchmark establishes no global quasipolynomial recognition bound.

## Retained proof replay

There are 52 saved JSON certificates, one per case and arm. The portable command is:

```sh
python -B topology_research/replay_benchmark_proofs.py \
  --benchmark ../../results/benchmark-final.json \
  --proofs ../../results/benchmark-final-proofs \
  --output reproduced/benchmark-proof-replay.json
```

The delivered `benchmark-proof-replay.json` records the corresponding saved-file
verification pass, including proof hashes and source hashes. Every saved proof
must match every associated warmup and measured proof hash before it is replayed
against the original triangulation and vector. This pass is verification, not a
second performance benchmark. The earlier `saved-certificate-replay.json` and its
driver `replay_saved.py` are retained as a separate completed replay record.
