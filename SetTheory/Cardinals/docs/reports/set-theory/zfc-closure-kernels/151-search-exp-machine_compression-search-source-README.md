# Reproducing the bounded runtime searches

**These are discovery experiments with negative results.** They do not prove that a 217-state solution is impossible. In particular, a collected set of windows from finite register representatives is not an invariant covering all natural register values. A positive preliminary fold would still need an appropriate unbounded simulation argument, logical calibration, and exact blank-start audit.

This folder contains the main C++ sources, a portable Python input/preliminary-fold checker, the exact 6,758-specification fold pool, the 540 and 315 joint near-miss records, and concise terminal receipts. It deliberately excludes compiled executables, full context datasets, and invariant bitmaps.

## Dependencies and fixed assumptions

Use Python 3 and GCC's C++17 compiler (`g++`); the C++ sources use `bits/stdc++.h`. No Python package installation is needed.

These C++ experiments are pinned to the supplied **baseline K218 table**, its 4,744 source sites, dispatcher 84, start state 0, halt label 254, and native state labels below 303. The frame collectors use gap 80, 130 unit-one spare blocks, and the exact 312,909-step baseline blank prefix. The local diagram searches use radius 7 and fuel 97. Do not apply the unmodified collectors to the DMN table or other differently initialized layouts. Do not apply these fixed-capacity C++ programs to tables containing state labels 303 or greater.

**Path edits:** no included script contains an absolute workspace path. Set the three input paths in the commands below to the corresponding artifacts in the parent archive. There is no need to edit Python or C++ source for the pinned experiment. The omitted full invariant inputs must come from the independently audited source-invariant package:

- `BASELINE_SITES`: baseline `sites218.json`, a list of `[path, operation, argument]` triples.
- `BINARY_INVARIANT`: `zero_abstract_invariant.json`, a list of 4,744 lists of reachable 9-bit support masks.
- `TERNARY_BITMAP`: uncompressed `zero_one_many.bin`, exactly 4,744 × 19,683 bytes, with nonzero bytes marking admissible configurations. Register 0 is the least significant base-three digit; digits mean zero, one, and at least two. Decompress the corresponding certificate first if it is distributed compressed.

The parent checkpoint supplies `../baseline-k218.tm`. Its SHA-256 is `2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f`.

## Build

Run from this directory:

```bash
mkdir -p build results
for source in support_contexts ternary_contexts tworow_loop_synth helper_repair joint_marker joint_common joint_prehelper joint_common_partial joint_prehelper_partial joint_second; do
  g++ -O3 -std=c++17 "$source.cpp" -o "build/$source"
done
```

## Generate the representative contexts

Supply your archive's paths in place of these placeholders:

```bash
BASELINE_SITES=/path/to/sites218.json
BINARY_INVARIANT=/path/to/zero_abstract_invariant.json
TERNARY_BITMAP=/path/to/zero_one_many.bin
python3 prepare_search_inputs.py frames --table ../baseline-k218.tm --sites "$BASELINE_SITES" --binary-invariant "$BINARY_INVARIANT" --output results/frame-input.txt
build/support_contexts results/frame-input.txt > results/binary-contexts.txt 2> results/binary-contexts.log
build/ternary_contexts results/frame-input.txt "$TERNARY_BITMAP" > results/ternary-contexts.txt 2> results/ternary-contexts.log
```

The binary collector uses values 1 and 2 for every positive register class. The ternary collector uses values 2 and 3 for every “at least two” class, with all such registers receiving the same chosen representative in each run. Each collector also includes the exact blank prefix. These are finite representative assignments; mixed arbitrary large values are not enumerated.

Expected final counters:

| Collector | Runs including blank prefix | Machine transitions | Distinct state/window contexts |
|---|---:|---:|---:|
| Binary | 684,369 | 947,007,793 | 91,766 |
| Ternary | 11,104,165 | 14,674,840,421 | 100,767 |

The ternary input generator ignores the binary mask lists and obtains its configurations from the bitmap. If only ternary contexts are needed, omit `--binary-invariant` when preparing `frame-input.txt`.

## Synthesize both keeper actions

```bash
python3 prepare_search_inputs.py sample --contexts results/ternary-contexts.txt --output results/ternary-sample.txt
build/tworow_loop_synth results/ternary-sample.txt 0 > results/ternary0.hits 2> results/ternary0.log
build/tworow_loop_synth results/ternary-sample.txt 1 > results/ternary1.hits 2> results/ternary1.log
python3 prepare_search_inputs.py verify --contexts results/ternary-contexts.txt --specs results/ternary0.hits --output results/ternary0-full-audit.json
python3 prepare_search_inputs.py verify --contexts results/ternary-contexts.txt --specs results/ternary1.hits --output results/ternary1-full-audit.json
```

Mode 0 uses identical head locations for a folded state. Mode 1 permits a two-cell head displacement when all incoming movements to the dropped state have the same direction. Both keeper actions are synthesized over binary writes, left/right movements, and retained working-state targets (the halt label is excluded from this particular action enumeration); returning internally to the keeper on the same read branch is permitted. The preliminary sample has 6,599 contexts. The original run produced 152 and 30 preliminary folds, respectively, and **zero** complete collected-window survivors. The portable checker was verified to reconstruct the byte-identical sample and reproduce both zero-survivor results. Copies of the preliminary records and full first-failure audits are included.

## Arbitrary helper repair of the existing fold pool

```bash
build/helper_repair results/binary-contexts.txt fold-pool.txt > results/helper-binary.hits 2> results/helper-binary.log
build/helper_repair results/ternary-contexts.txt fold-pool.txt > results/helper-ternary.hits 2> results/helper-ternary.log
```

For each of the 6,758 fold specifications, the program traces the first failing candidate window, tries every binary write, left/right movement, and retained-working-state target for each touched non-keeper helper row (excluding halt-target repairs in this program), and accumulates counterexample windows. Both domains produced the same final counters: 40,563,473 repair proposals, 48,941 initial-witness passes, and zero complete collected-window survivors. This is not a search over all possible pairs of mutated rows: the fold pool and helper-row trace are explicit restrictions.

## Focused joint synthesis for states 13 and 108

```bash
build/joint_marker results/ternary-contexts.txt 13 108 0 all > results/joint-13-108-0.hits 2> results/joint-13-108-0.log
build/joint_marker results/ternary-contexts.txt 13 108 -2 all > results/joint-13-108-m2.hits 2> results/joint-13-108-m2.log
build/joint_marker results/ternary-contexts.txt 108 13 0 all > results/joint-108-13-0.hits 2> results/joint-108-13-0.log
build/joint_marker results/ternary-contexts.txt 108 13 -2 all > results/joint-108-13-m2.hits 2> results/joint-108-13-m2.log
```

Arguments are `contexts keeper drop head_shift all`. The final `all` selects all 432 eligible helper rows; omitting it restricts helpers to rows reached on the old local traces. Both keeper actions and one arbitrary helper action are synthesized jointly. The four runs total 12,054,528 first templates and 10,675,896 second-action alternatives, with zero complete survivors. The same counts occurred on the binary context set.

## Common-branch joint helper families

```bash
build/joint_common results/binary-contexts.txt results > results/common.hits 2> results/common.log
build/joint_prehelper results/binary-contexts.txt results > results/prehelper.hits 2> results/prehelper.log
```

Both programs consider the 262 state pairs with exactly one shared action after state identification. They retain that action and jointly synthesize the other keeper action with an arbitrary helper row. `joint_common` targets the helper directly; `joint_prehelper` permits one existing predecessor of the helper as the initial target. The second argument is an output directory for any complete candidate table.

The direct family checked 394,785,792 combinations; 540 passed folded-state windows and none passed helper contracts. The predecessor family checked 738,946,752 combinations; 315 passed folded-state windows and none passed helper contracts.

## A second helper repair

The `*_partial.cpp` versions reproduce the preceding families while also emitting their folded-state near misses. Their extra `PARTIAL` lines are inputs to `joint_second`.

```bash
build/joint_common_partial results/binary-contexts.txt results > results/common-partials.txt 2> results/common-partials.log
build/joint_prehelper_partial results/binary-contexts.txt results > results/prehelper-partials.txt 2> results/prehelper-partials.log
build/joint_second results/binary-contexts.txt results/common-partials.txt results > results/second-common.hits 2> results/second-common.log
build/joint_second results/binary-contexts.txt results/prehelper-partials.txt results > results/second-prehelper.hits 2> results/second-prehelper.log
```

To avoid regenerating the two larger enumerations, use the supplied `common-near-misses.txt` and `prehelper-near-misses.txt` instead. The second-repair runs checked 1,812,016 and 1,170,224 proposals respectively, with zero complete survivors.

## Data formats and receipt limitations

A context file begins with the number of working states, followed by rows
`q w0 d0 z0 w1 d1 z1`, then a context count and pairs `q window`.
A window is a 15-bit integer; bit 7 is the currently scanned cell. Directions are −1 and +1.

A fold-pool record is
`HIT keeper drop shift w0 d0 z0 w1 d1 z1`.
A joint near-miss record is
`PARTIAL keeper drop w0 d0 z0 w1 d1 z1 helper_state helper_bit helper_write helper_direction helper_target`.

`receipts/` contains terminal excerpts, not complete execution transcripts. Its manifest records the SHA-256 and line count of each original full log. Counts of the different families overlap and must not be added as counts of distinct machines. Elapsed times are machine-dependent. All complete-survivor counts are zero; partial counters have only the meanings defined above.
