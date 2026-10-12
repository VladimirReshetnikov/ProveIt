# Why the small Pachner cut is slow

`pachner_terminal_profile.json` and its text companion preserve one complete
`pachner23_5_8_2/mixed` group-terminal query under cProfile: source construction,
certificate production, compact JSON serialization/loading, and replay through
the existing `verify_normal_cut_handlebodies` dispatcher.  It succeeds and its
certificate is 387,809 bytes.  Imports and fixture loading were excluded.

**These are instrumented diagnostic costs, not benchmark medians.**  cProfile
substantially changes execution costs, particularly with millions of small
Python calls.  The separate complete-query benchmark remains the performance
measurement.  The profile identifies where work occurs.

## Disjoint stages in the single profiled call

| Stage | Profiled inclusive seconds |
|---|---:|
| Source parallelity producer | 0.736508 |
| Source moment-boundary producer | 1.128844 |
| Independent parallelity source checker | 0.816691 |
| Independent moment-boundary source checker | 0.874380 |
| New finite terminal producer, including presentation compilation | 0.001621 |
| Independent finite source-presentation checker | 0.001032 |
| Independent finite group checker, all three components | 0.000448 |
| JSON serialization and loading | 0.043589 |

The complete instrumented query took 3.613803 seconds: 1.867185 producing,
0.043589 saving/loading JSON, and 1.702236 independently replaying.  The four
disjoint inherited source stages account for **3.556422 seconds, 98.4%** of
this profiled wall time.  The three disjoint new finite stages total
**0.003101 seconds, 0.086%**.  Other wrapper and metadata costs occupy the
small remainder.  Cumulative costs from nested routines elsewhere in the
profile must not be added to these disjoint stage totals.

The 16-generator, 14-relator, 27-letter active presentation is indeed tiny.
Only one of its three components needs substitution search: 14 candidate
trials, 134 trial-letter visits, two substitution pivots and two private
pivots.  The second component uses ten private pivots and the third is
already free.  Optimizing this word reducer cannot explain away the measured
whole-query slowdown.

## Two concrete inherited loops

1. `interval_orbits.py:_contract` runs **1,161 times**, with 0.391698 seconds
   self time and 1.042184 seconds inclusive time.  Its implementation sorts
   all current pairing-support intervals and scans their union on every
   call, even when the union has no static gap.  The five orbit discovery
   queries consume 1,166 total cycles.  The moment-boundary query alone starts
   with 668 pairing records and needs 485 cycles.  These numbers identify
   repeated support reconstruction as a concrete production target.

2. `weighted_orbit_verify.py:_translation_fold` runs **884 times**, taking
   0.515789 seconds inclusively.  It rebuilds retained prefix jump events via
   `_prefix_events`, scans the current weight runs for suffix contributions,
   and integrates a newly sorted jump set.  Together with reflection folds,
   `_prefix_events` runs **1,161 times** and takes 0.472637 seconds inclusively.
   The weighted verifier makes 265,778 vector additions.  Preserving or
   incrementally updating an independently checked prefix representation is a
   more relevant checker optimization than changing the finite group policy.

The entire profile records 13,846,179 Python calls.  Its exclusive module
table charges 1,982,974 default polling-callback calls (0.094419 seconds) to
the lambda defined in `normal_cut_groups.py`, although the calls originate
inside the inherited source algorithms.  For that reason, the exclusive
module-category totals should not be interpreted as an exact division
between new algebraic work and inherited source work; use the disjoint
functional stages above.

## Proof size and next experiments

The parallelity and boundary source proofs occupy 278,271 and 106,453 bytes.
Their sum, 384,724 bytes, is **99.2%** of the complete certificate.  The finite
presentation occupies 1,576 bytes and all free-group proofs together 944
bytes.  The large source proof therefore matters for storage and replay,
while JSON conversion itself accounts for only about 1.2% of the instrumented
query; serialization is not the principal time bottleneck.

The immediate research targets are to reduce repeated interval-support scans,
reuse verified prefix event data during weighted replay, and investigate a
verified explicit-universe path for sufficiently small orbit universes.  Here
the largest recorded orbit-universe size has only ten bits.  A hybrid path
could expand only when that finite universe is bounded by a fixed polynomial
in encoded input size, preserving a polynomial size guard while retaining
compressed algorithms on large binary inputs.  This is a proposal requiring
its own source/certificate implementation and tests, not an optimization
implemented in this package.

No production source was edited for this diagnosis.  Reproduce with:

```bash
python tools/profile_terminal.py --fast-root /path/to/ProveIt/Topology/UnknotRecognition/fast \
  --case pachner23_5_8_2/mixed --output /tmp/pachner_terminal_profile.json
```
