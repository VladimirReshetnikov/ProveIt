# Optimization artifacts: finite engineering evidence

This directory is self-contained for the commands below. Python 3.10 or newer
and its standard library suffice for the default replay. Assertions must be
enabled: do not use -O or -OO. The optional long literal-tape diagnostics also
need a C++17 compiler.

**No new consistency-machine state bound is established here.** The 268-state
table is an engineering control retaining the original equality-bearing logical
program under layout changes. The three 252-state tables are prepared-tape or
local-macro experiments with unsuccessful bounded blank-bootstrap diagnostics.
None is a newly calibrated 252-state consistency machine.

## Recommended quick replay

Run from this directory:

    python3 -B reproduce.py --record replay_verification.json

This checks the source manifest, regenerates the selected 268-state control,
compares its table, DAGs, labels and RM certificate byte for byte, independently
checks all 4,533 RM certificate pairs, and runs:

| Check | Finite coverage |
|---|---|
| Tail-entry search | All 1,008 choices of write bit, direction and retained target state |
| Independent decrement macro | 6,576 cases; 1,859,630 literal TM moves |
| Runtime decoder sites | 8,391 symbolic cases: 8,387 normal, 3 overflow, 1 halt |
| Bootstrap input integrity | All 6,460 decoder paths and 100,001 directly generated RM configurations |
| Rotation-selected artifact | Recreates the retained initial DAG with zero heuristic iterations |

The default command does not repeat the 50,000-rotation search, the
10,000-proposal schema search, or the long C++ bootstrap searches. Its generated
268-state table has SHA256:

    77f88b15383b13846090a31f3780673daf57c8b66fed2b9e7de252686901a61d

The recorded replay succeeded from this packaged layout without network access.
The local tail and site scripts rewrite their adjacent deterministic JSON
results; the replay compares those results with the supplied bytes. Compiler
outputs are generated in a temporary directory.

## Artifact map and scope

| Path | Contents and meaning |
|---|---|
| control268/ | Selected source-19 268-state recipe, named and numeric tables, both RM DAGs, the 4,533-pair certificate and historical evidence |
| schema_search/ | Recorded 10,000-proposal search; it retained the same 268-state artifact |
| rotations268/ | Recorded 50,000-proposal closed-subprogram rotation search; best predicted count remained 268 |
| rotate_slp.py | Reassociates only triples whose break/continue bounds are zero; uses a backend-derived state-count proxy |
| search_tail_entries.py | Tests local prefixes for old97/read0; three accepted suffix shapes are [0], [1], and [0,0] |
| audit_tail252.py | Independent literal-tape tests of the append-[1] positive-decrement macro |
| runtime252_site_replay.py | Replays the runtime-only deletion of old5 with old49/read1 routed directly to old64 |
| bootstrap/ | Direct interpreters, exact finite input data, and bounded blank-run logs |
| vendor/ | Exact pinned upstream sources, minimal ProveIt dependency layout, and original license notices |

The symbolic runtime test uses the published executor and its register-box
contracts. It is finite executable evidence, not a new kernel theorem. The
append-[1] macro tests are separate; the site checker does not silently replace
its old decrement oracle with a new one.

The literal tables use old state labels, which are not consecutive. There are
252 distinct working states and 504 rows in each; old254 is the terminal label.

- candidate252-runtime.tm deletes old5 and restores old49/read1 to (0,R,64).
- candidate252_tail_oldlabels.tm additionally changes old97/read0 to (1,L,112),
  appending a spare block of value 1.
- candidate252_tail00_oldlabels.tm instead uses (1,R,112), appending two spare
  blocks of value 0.

These local runtime changes do not supply a correct blank initializer. Early
spare data can become active register data during self-initialization.

## Exact control regeneration and independent certificate check

The source-19 driver and its dependencies are included unchanged. This command
replays its selected recipe without a heuristic search:

    python3 -B vendor/source19/full_logic_search.py \
      --repo vendor/proveit \
      --prior vendor/one_schema_machine \
      --output /tmp/zfc-control268-replay \
      --iterations 0

The independent path-engine check is:

    python3 -B vendor/source19/verify_schema_rm_certificate.py \
      --prior-machine-dir vendor/one_schema_machine \
      --reference /tmp/zfc-control268-replay/full_logic_reference.dag.json \
      --candidate /tmp/zfc-control268-replay/full_logic_best.dag.json \
      --certificate /tmp/zfc-control268-replay/full_logic_rm_certificate.json

This proves the stated finite certificate checks, not the complete binary
compiler simulation or ZFC calibration.

Historical generator/helper hashes need one explicit provenance qualification:
the exploratory runs used copies with one extra final newline each. The
packaged driver and helper are the exact pinned Git originals. Their regenerated
tables, DAGs, labels and certificates are identical. The replay verifies this
and records both hash pairs. Elapsed times naturally vary.

## Optional search repetition

The recorded rotation search can be rerun with:

    python3 -B rotate_slp.py \
      --input control268/full_logic_best.dag.json \
      --output /tmp/zfc-rotations-replay \
      --iterations 50000 --seed 20261016

This command uses a state-count proxy; each individual proposal is not compiled.
Failure to improve 268 is a bounded search result, not an optimality theorem.
The saved rotations search JSON has only its input path rewritten for this
layout; its measured results are retained.

The recorded schema search can be rerun by adding:

    --iterations 10000 --rng-seed 10616

to the control-regeneration command and selecting a different output directory.

## Bounded blank-bootstrap diagnostics

The pure Python four-million-step append-[1] diagnostic is optional:

    python3 -B reproduce.py --bootstrap-four-million \
      --record replay_with_four_million.json

The C++ engine takes one literal transition per iteration. It scans eight
specified old-label entry states; it deliberately does not use only the start
directive in the table. It has a finite step limit and a tape-excursion cutoff.
Its frame recognizer compares with the supplied finite RM prefix.

First verify the input data:

    python3 -B bootstrap/verify_inputs.py

The runtime path catalogue is reconstructed from the pinned
Prog254.v decoder, not the differently bracketed shared Dag254.v used by the
compiler experiment. The reference prefix is regenerated with the included
direct register interpreter. Their semantics are related upstream, but their
instruction path strings must not be identified.

From the bootstrap directory, the exact long commands are:

    c++ -O3 -std=c++17 search_tail_boots.cpp -o /tmp/zfc-tail-boots
    /tmp/zfc-tail-boots ../candidate252-runtime.tm 100000000
    /tmp/zfc-tail-boots ../candidate252_tail_oldlabels.tm 100000000
    /tmp/zfc-tail-boots ../candidate252_tail00_oldlabels.tm 1000000000

Their historical outputs are in logs/, with matching descriptive filenames.
These are bounded negative diagnostics. They do not prove that a later handoff,
another invariant, or another initialization can never work. No acceleration
experiment or accelerated trace is included.

## Pins, files and changes

The host source pin is ProveIt:

    4747142d5d15213eb711bdadfa3cc7e769fcb7a7

The public 253 generator and runtime-source pin is busy-beaver PR20:

    0d544f2a2e3c18f12278441a74b7879f31cbe856

The host's pinned public Wade backend and shared DAG derive from:

    297ab8df7e5de329605c3875b4934643b371a5e3

source_manifest.json records origin paths, pins, byte counts and SHA256 hashes.
Vendored originals remain byte-exact. The minimal pseudo-repository includes
only the import/data closure needed by the source-19 command, not the full host
checkout. Source-19 and source-08 files retain their content under simpler local
filenames.

Our search_tail_entries.py, audit_tail252.py and the exploratory Python
bootstrap script change only filesystem paths. The new replay wrappers connect
the packaged inputs and compare finite evidence. Original license notices are
retained under vendor/. The parent archive's report explains the mathematical
and formal-proof boundaries.
