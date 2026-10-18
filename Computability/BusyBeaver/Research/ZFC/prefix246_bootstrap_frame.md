# Exact 246-state bootstrap frame

`BootstrapFrame246.bootstrap_frame` identifies the complete blank run at 410,735 steps with the dispatch frame of `LogicalSeed246.initial`. The head is at −5; the zipper has left/right padding 10/0, gap 181, and 167 spare registers of value one. The physical register values are `[0,0,0,3,0,0,3,0,0]`. Equality includes the zero exterior of the infinite tape.

The proof uses the completed [bootstrap chain](boot_prefix246.md), the separately calibrated logical seed, and the generic `Permutation252Frame` representation. The strict guard selects 113 actual project imports from 123 candidate providers. It excludes the unrelated Site/Symbolic executor modules present in the Frame evidence. Init and Lean's Omega tactic are the two explicit toolchain boundaries.

The successful source/audit attempt passed five named axiom probes and five typed callers, with no warnings, in 0.832 and 0.456 seconds. Three probes have no axioms; `target_zip` uses `propext`, and `bootstrap_frame` uses `propext` and `Quot.sound`. The fresh source object was recorded before the audit and remained unchanged afterward. All 239 recorded inputs were checked before and after execution and independently rehashed during review.

The first actual attempt failed because the `seed_tail` simplification did not unfold `LogicalSeed246.initial`. Its source log, record, source, audit and guard remain in [the history](results/prefix246-bootstrap-frame-history.json). The repair adds only that definition to the simplification set; all theorem statements are unchanged. The successful retry's source/audit/guard snapshots were frozen before execution. The history preserves both attempts and the repair record.

The [successful record](results/prefix246-bootstrap-frame-verification.json) retains its actual scratch paths for the three supplied parent records. The [review](results/prefix246-bootstrap-frame-review.json) separately records the source and evidence assessment. Publication preserves the exact successful source and audit; the portable guard changes only their default paths. No proof rerun occurs during publication.

With the exact providers recorded in the parent evidence still available, the maintained preparation command is:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_prefix246_bootstrap_frame.py \
  --repo "$PWD" \
  --bootstrap-evidence Computability/BusyBeaver/Research/ZFC/bootstrap-prefix246/attempts/group08/run1/verification.json \
  --seed-evidence Computability/BusyBeaver/Research/ZFC/results/prefix246-logical-seed-verification.json \
  --frame-evidence Computability/BusyBeaver/Research/ZFC/results/prefix246-frame-verification.json \
  --output /tmp/zfc-prefix246-bootstrap-frame-prepared \
  --prepare-only
```

Preparation checks hashes and provider selection without a compiler or version query. Omitting `--prepare-only` executes the bounded source/audit pair with one thread, 4,096 MiB and a shared 120-second wall limit under Lean's default proof limits. Objects are explicit prerequisites; this guard does not rebuild dependencies.

This unit closes the blank-start dispatch-frame identification. Whole-program coverage, runtime composition, the consistency endpoint and its PA representation are separate obligations.
