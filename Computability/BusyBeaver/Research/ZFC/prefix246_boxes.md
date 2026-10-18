# Unbounded register contracts for prefix246

`Prefix246Boxes.lean` proves the three register excursions directly on the exact 246-state table. Every contract covers arbitrary natural register values, arbitrary finite left context and the complete zero-exterior tape. Increment appends a value-one spare. Positive decrement retains the spare suffix and moves the file boundary one cell right. Zero decrement restores the original file, exits in old112, and explicitly requires a following block of arbitrary value.

The exact durations are `2 * width (pre ++ v :: rest) + 7` for increment, `2 * width pre + 4` for positive decrement, and `2 * width pre + 7` for zero decrement. The proof retains the checked 250-state prefix/suffix inductions; the folded blank pulse uses old255/read1 in place of deleted old97/read1. Pure encodings and the table-parametric return scanner are reused from the attributed permutation252 infrastructure. No execution theorem about the 252-state machine is used as an execution theorem about this table.

Root's first source/audit run passed: 14 named axiom probes and 19 typed callers, with standard Lean axioms only. Source took 1.699 seconds and audit 0.622 seconds. Seven inherited unused-simp warnings remain in the exact successful source; the audit has zero warnings. The guard keeps one thread, 4,096 MiB, a shared 120-second budget and default proof limits, with no dependency builds or version query.

The exact closure contains eight project providers, with Init and Lean.Elab.Tactic.Omega as toolchain boundaries. All 28 recorded input identities and actual first providers were rechecked, and the fresh source object was recorded before its audit. The sole successful attempt and raw snapshots are retained. An independent full source/audit/interface review is embedded verbatim in the author final evidence review. The comment-only source58 attribution correction predates the sole proof run.

From the repository root, using a new external output directory:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_prefix246_boxes.py \
  --repo "$PWD" \
  --pulse-evidence Computability/BusyBeaver/Research/ZFC/results/prefix246-pulse-verification.json \
  --output /tmp/zfc-prefix246-boxes-check --prepare-only
```

Preparation checks bindings without running Lean or querying its version. Removing `--prepare-only` requests the bounded source/audit proof check. Publication retains the successful source/audit bytes and changes only the guard's two default paths. The retained successful record identifies the actual scratch Pulse evidence used during that run; the identical maintained record can be supplied above.

These local contracts do not establish complete decoder coverage, the exact blank bootstrap, a binary consistency theorem or PA internalization. Attribution includes Mira-Cult, Jeff Ketchersid and Wade's machine/framework, source58's shared carry, and source63's contextual folds.
