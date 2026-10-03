# Bounded evidence and replay results

All final implementation and test checks passed normally and under Python -O.
The evaluator remained unchanged throughout final testing:
SHA-256 `785082d121622f8fc755ed7039ee6efe719964296eec7d76ad44495dc5c6c2c1`.

## Small-source eager comparisons

`test_sparse_parallel.py`, 54.252 s normal / 50.512 s optimized:

- 10 sources; 1,140 arithmetic/eager template equalities
- 8,183 configurations; 16,366 candidate-map, active-map, block-output,
  block-involution, whole-step and inverse checks each
- 2,280 endpoint orientations and 2,280 endpoint-plus-spoiler configurations
- 3,072 exhaustive malformed subsets over 11-site and 10-site universes
- 192 encoded states; 120 random supports; 20 huge-coordinate translations
- 1,761 local-radius comparisons; 162 guard-detector configurations
- 259 API/mutation rejections; 19 source-validation parity checks
- 32 instrumented raw-probe bound cases: n+2 without verification, 2n+4 with
  verification, including empty/singleton, prospective rejection, competition,
  encoded states, and three separated copies; maximum observed 8 / 16 calls
- Eager/ordered-execution sentinels: a 780,035-type source constructed zero
  endpoint templates; bounded runtime queries touched only 5 distinct types

The malformed cascade fixture {-118,-112,0,18,23} is fixed by the new rule,
despite movement under the old ordered rule. Candidate equality includes
labels and invariant integer anchors, not just final roundtrips.

## Independent audit suite

`audit_candidate_completeness.py`, final external-output replay
3.796 s normal / 4.156 s optimized:

- 14 varied source cases
- 17,504 contained-endpoint discovery checks
- 1,120 full candidate key/orientation maps against all-index literal matching
- 2,240 actual block candidate/selection/output comparisons
- 2,560 sparse/literal domain and image guard comparisons

The all-index oracle is small-source and test-only. The independent audit of
the runtime and symbolic completeness/cost proofs found no correctness defect.

## Universal source startup

Only `benchmark_universal.py` needs `universal-source.json` and the stored
valid-state trace. The source is 32,034,272 bytes, SHA-256
`fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3`.

Its exact parameters are m=122,622, p=66,066, a=75,495, J=0;
F=269,291,358,255 endpoint types and new radius R=91,711,698.

Normal / optimized final receipts record:

- Metadata compilation: 3.914 / 7.033 seconds
- 128 literal startup steps, with inverse verification and equality to the
  pinned old valid-state trace: 0.136 / 0.194 seconds
- 128 arbitrary endpoint/noise configurations sampled across the type range,
  including a 2,048-bit negative translation: 0.118 / 0.168 seconds
- Total benchmark wall time: 4.532 / 7.853 seconds
- Peak process RSS: 376,776 / 378,012 KiB
- At most 4 discovered candidate types, 2 raw keys, 2 selected keys and
  2 prospective probes per block in these bounded runs

Old ordered execution and eager construction entry points were replaced with
raising sentinels before compilation. The source metadata was built directly;
no F-element array, full local truth table, or source-boundary shortcut was
used. Timings include ordinary machine/run variation; the optimized run's
longer compilation is not a semantic distinction.

This is only a 128-step prefix. No whole universal startup, Turing step, halt,
or eager universal comparison is claimed. The malformed checks are roundtrip
corroboration; general equality rests on the proof and small-source eager tests.

## Exact commands

Run from this directory, or pass absolute script paths. The complete commands
below preserve the frozen packet, using external receipts and no bytecode:

    python -B verify_bundle.py
    python -B test_sparse_parallel.py --output-dir /tmp/sparse-parallel-replay
    python -B -O test_sparse_parallel.py --output-dir /tmp/sparse-parallel-replay
    python -B audit_candidate_completeness.py --output-dir /tmp/sparse-parallel-replay
    python -B -O audit_candidate_completeness.py --output-dir /tmp/sparse-parallel-replay
    python -B benchmark_universal.py --output-dir /tmp/sparse-parallel-replay
    python -B -O benchmark_universal.py --output-dir /tmp/sparse-parallel-replay

The main and independent audit suites do not read the 32 MB universal source.
Bundle hash verification does read it to verify integrity, without parsing it.
All imports and inputs are adjacent packet files. No network access or sibling
release directory is needed. Standard library only. Checks use explicit raises
and remain enabled under optimization.
