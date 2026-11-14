# Additional bounded state-elimination searches for PA196

**Result: no machine with fewer than 196 working states was obtained.** These files add stronger source-derived window contexts, a predecessor-boundary elimination template, and two ways of storing a deleted control state's identity in the head position or tape. They are reproducible experiments, not a proof that PA196 is minimal or a new PA consistency theorem.

## Reproduce

Requirements: Python 3.10 or later, a C++17 compiler named `g++`, and no Python optimized mode. No network, third-party Python packages, Lean installation, or other repository checkout is needed.

```sh
python3 replay.py --output /tmp/pa196-local-search --radius 6
```

The output directory receives regenerated context sets, search receipts, compiler products, and progress logs. It must be outside this package if you want to preserve the supplied files unchanged. The full run takes about a minute in the recorded environment; elapsed time is not a correctness criterion.

For a baseline check without compilation or state-reduction search:

```sh
python3 replay.py --quick --output /tmp/pa196-baseline-check
```

This rechecks the input hashes, all baseline symbolic cases, exact startup, and the radius-two context census (about ten seconds in the recorded environment).

For just the small positive and adverse controls:

```sh
python3 replay.py --controls-only --output /tmp/pa196-local-controls
```

The controls require the scanners to recognize exact duplicated states, a three-step implementation using a head offset of minus two, and a three-step implementation that restores a complemented neighboring bit. Changing a helper direction or restoration bit must invalidate the corresponding claimed witness. The controls are checks of these specific templates, not a general verification of the C++ programs.

## Frozen inputs and trust boundary

`input_pins.json` pins the literal table, Lean program, native-label conjugacy, and imported symbolic interpreter. The literal PA196 table has SHA-256 `e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8`. The source is James Chang's `jamesyc/BusyBeaver` commit `407cdc356f6b586635e71ac92be394255f4bfea4`.

The symbolic interpreter is the unchanged `verification/symbolic.py` from the supplied ProveIt archive `pa_consistency_research_2026-11-13.zip` (archive SHA-256 `466c804d54495d3347252a98788af021aecc459b041fcc1733b3adf1ff1e943b`). It is an executable port of the published `M6/Runtime.lean` abstraction. Its register-box oracle assumes the established engine contracts. This package **does not** rebuild those Lean proofs or turn the Python results into new Lean or PA certificates.

`source_contexts.py` rechecks all 4,959 symbolic cases for the 3,812 source sites and simulates all 58,154 startup transitions, checking the exact final clean frame. For ordinary decoder states it collects every local word represented by the symbolic configurations. Variable-length unary runs are overapproximated, and an opaque box supplies all possible words. For every state that appears in an opaque engine contract or has a self-loop that the interpreter can skip, it instead retains the full blank-start window closure. Thus it never treats a finite sampled register value as a universal invariant. The final context sets are also checked to be subsets of the coarse blank-window closure.

The coverage argument is mathematical but not newly kernel checked. Its assumptions are the correctness of the imported symbolic interpreter, its engine contracts, the finite source coverage calculation, and the exact startup calculation. None of the observed negative search results needs an assertion that every abstract window is actually reachable.

## Search templates

- `fold_general.cpp`: identify one state with another; change at most one retained row. Compare a positive child block with one parent transition, preserving the complete finite tape window and head.
- `fold_two_general.cpp`: allow both retained rows to change, with an unknown-row prefilter. The prefilter preserves candidates that could be resolved by the second row. This is an adaptation of the supplied ProveIt two-row scanner; provenance is in `NOTICE.md`.
- `predecessor_elimination.py`: delete a state with a unique incoming row and alter that predecessor action; compare against the old two-transition block, so the eliminated state need not be an alignment point.
- `predecessor_multiblock.py` and `multiple_predecessor_elimination.py`: permit later old endpoints and try each incoming predecessor action separately. A proposed deletion is abandoned when one predecessor has no witness. Mutually dependent simultaneous predecessor changes are not exhaustively searched.
- `fold_shift.cpp`: for a deleted state whose incoming transitions all have direction `d`, use a head displacement `-2*d` for that state and reverse the incoming directions. Synthesize one retained row.
- `fold_bitphase.cpp`: for the same direction condition, complement the cell immediately behind the incoming movement. Incoming rows complement their written bit, and the deleted-state simulation relation carries that one tape-bit difference. Synthesize one retained row.

All returned matches must keep every read within the declared window and take between one and 64 new transitions. These bounds can reject valid larger transformations. No script searches all 195-state machines. The source-derived contexts are independent of any conjectured smaller machine.

## Recorded results

The historical receipts in `receipts/` distinguish the exact configurations that were run before packaging. `replay.py` regenerates the principal radius-six suite with the same input bytes and writes a fresh combined receipt; times may differ.

| Context radius | Source-derived windows | Coarse blank-window windows |
|---:|---:|---:|
| 2 | 2,412 | 2,848 |
| 4 | 17,343 | 25,827 |
| 6 | 161,614 | 270,067 |

At radius four, the one-row scanner tested 59,928,960 patches with a 64-step bound, with no survivor. At radius six, the two-row scanner tested 29,964,480 first-row actions, retained 81,874 for the second-row stage, and tested 64,189,216 complete row pairs; there was no survivor. The head-offset and neighboring-bit encodings each tested 52,590,720 one-row variants in their recorded runs and found none. Their input context radii are explicit in the receipts. The packaged full replay additionally repeats all four C++ templates at radius six; it reproduces zero survivors. Its combined receipt is `receipts/portable_radius6.json`.

The package does not contain a purported 195-state transition table. A negative result under these finite templates is not a state lower bound and does not settle whether another calculus, layout, engine, or initialization can beat 196 states.
