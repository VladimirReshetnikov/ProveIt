# Checked transfer from loop-rotation 244 to combined 243

Lean checks the exact two tables and proves that the combined 243-state machine
halts from blank tape if and only if the loop-rotation 244-state machine does.
This is a relative machine equivalence. Calibration of this rotation table to
ZF refutation remains a separate Lean obligation, as does internalization in PA.
The already checked [compensated 244-state endpoint](compensated244_binary.md)
uses a different 244-state table.

| Unit | Checked scope | Named probes / typed callers |
| --- | --- | --- |
| [TableRotation244](../../Lean/BusyBeaver/ZFC/TableRotation244.lean) | Exact 244 states, 488 actions, start/dispatcher and unique halting row | 7 / 7 |
| [TableCombined243](../../Lean/BusyBeaver/ZFC/TableCombined243.lean) | Exact 243 states, 486 actions, retained-state embedding, 480 common actions and local rows | 53 / 6 |
| [Rotation244Invariant](../../Lean/BusyBeaver/ZFC/Rotation244Invariant.lean) | Local left-bit invariant preserved at every time from old state 95 | 5 / 8 |
| [Combined243Blocks](../../Lean/BusyBeaver/ZFC/Combined243Blocks.lean) | Seven complete-configuration paired blocks and seven new endpoints | 14 / 14 |
| [Combined243Simulation](../../Lean/BusyBeaver/ZFC/Combined243Simulation.lean) | Positive-block simulation and halting/nonhalting equivalence from the common start, including blank tape | 4 / 4 |

The five actual source/audit pairs pass with zero warnings: **83 named probes
and 39 typed callers**. Their source and audit files are published unchanged.
Raw records are available for the [rotation table](results/combined243-table-rotation-verification.json),
[combined table](results/combined243-table-combined-verification.json),
[invariant](results/combined243-invariant-verification.json),
[blocks](results/combined243-blocks-verification.json), and
[simulation](results/combined243-simulation-verification.json).
Only standard Lean axioms occur; no `sorry`, `native_decide`, or raised global
proof limits is used. Exact attempts, preparation records, logs, source
snapshots, guard adaptations, and role-disclosed reviews are preserved in
[combined243-formal](combined243-formal/).

The rotation proposal comes from `d91a27b462`; its QT loop transformation
removes old state 26 from routed 245. Applying the compensated-routing change
from `248bc05936` removes old state 122 as well. The combined table has canonical
states 0–242, start 0 and dispatcher 87, with separate halting target 243.
Its embedding into rotation 244 skips canonical state 112 (old label 122)
and preserves the entire head and tape. The table's total old-label lookup
fallback on absent labels does not introduce extra states.

The invariant says that old states 68 and 167 have a one immediately left of
the head; at old state 81, a one immediately left implies a one two cells left.
The local blocks preserve the complete configuration after positive durations
on both sides. The global proof reuses
[PositiveBlockBisimulation](../../Lean/BusyBeaver/ZFC/PositiveBlockBisimulation.lean)
and explicitly excludes the intermediate checkpoint at old state 92.
It covers arbitrary heads and finite-support `Core` tapes at old state 95,
including arbitrary list representations and blank tape. It makes no claim
about arbitrary infinite-support tapes or equal elapsed times.

The rotation table's first actual attempt failed while writing its target
object because the new output subdirectory was absent. The retained successor
guard creates that directory. Source and audit were unchanged, and the second
actual attempt passed. The temporary suggestion to add an Omega import to the
invariant was withdrawn before any source edit or execution. These events and
unexecuted authoring drafts remain in the history; they are not hidden proof
retries or additional successful units.

The guards select respectively 1, 2, 2, 3 and 7 project providers, with the
recorded Init/Omega boundary for each unit. Every source/audit pair shares
120 seconds and runs serially with `-j1 -M4096`; fresh source objects are captured
before the audit and all selected inputs/providers are checked afterwards.
No compiler-version query, dependency build, or download is performed.
The guards require the exact compiler and existing cached providers named in
their boundaries, including historical scratch paths. They do not distribute
compiled caches or bootstrap a clean checkout.

From this directory, use a new external output directory for each invocation:

```sh
python3 -B check_table_rotation244.py --prepare-only --output /tmp/rotation244-prepared
python3 -B check_table_rotation244.py --output /tmp/rotation244-actual
python3 -B check_table_combined243.py --output /tmp/combined243-table-actual
python3 -B check_rotation244_invariant.py --output /tmp/rotation244-invariant-actual
python3 -B check_combined243_blocks.py --output /tmp/combined243-blocks-actual
python3 -B check_combined243_simulation.py --output /tmp/combined243-simulation-actual
```

The installed guards change only discovery and default source/audit/boundary
paths; exact diffs accompany the executed originals. Preparation performs no
proof compilation. The ordinary manuscript and separate runtime checks can
support a broader mathematical argument, but this five-unit Lean packet alone
does not prove a ZF-consistency endpoint, unconditional nonhalting, or independence.
