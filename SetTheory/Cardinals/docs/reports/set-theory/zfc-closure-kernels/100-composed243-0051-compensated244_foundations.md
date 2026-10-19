# Lean foundations for the compensated 244-state machine

Three checked units support the transfer from the verified routed 245-state
machine to the compensated 244-state candidate from `248bc05936`.
The complete 244-state halting-equivalence theorem remains in progress.

| Unit | What Lean proves | Named probes / typed callers |
| --- | --- | --- |
| [PositiveBlockBisimulation](../../Lean/BusyBeaver/ZFC/PositiveBlockBisimulation.lean) | A relation that matches halting and advances both machines by positive blocks preserves halting, with an explicit blank-start specialization. | 4 / 4 |
| [Routing245Invariant](../../Lean/BusyBeaver/ZFC/Routing245Invariant.lean) | The original machine's local left-bit invariant holds at every time from the common start, for arbitrary head and finite-support tape. | 5 / 8 |
| [TableCompensated244](../../Lean/BusyBeaver/ZFC/TableCompensated244.lean) | The exact 244-state/488-row table, retained-state embedding, 482 common transitions and required literal local rows. | 53 / 6 |

All three actual source/audit runs pass with zero warnings and only standard
Lean axioms. The source/audit times are respectively 0.558/0.442,
9.369/0.275 and 14.023/0.434 seconds. Their exact records are
[generic](results/compensated244-positive-blocks-verification.json),
[invariant](results/compensated244-invariant-verification.json), and
[table](results/compensated244-table-verification.json).
The source and audit files are byte-identical to those executions.

The table is the principal compensated variant. Canonical states are 0–243,
start 0, dispatcher 88, with separate halt target 244. Its old labels delete
122 from Routing245 and change four retained rows. The embedding skips old
canonical state 113 and preserves the entire head and tape. The root's separate
parser comparison confirms all 488 delivered actions and all 244 old labels.
The old-label lookup has a total fallback on absent labels; those fallback
values are not extra states. Neither the alternative 244 tables nor a new
source theory are substituted.

The invariant says that old states 68 and 167 have a one immediately left
of the head, and at old state 81 a one on the left implies another one two
cells left. It is derived from the complete incoming transitions and preserved
by every step. The generic proof uses induction on an actual halting time;
absorbing halt handles a halt inside a block. No bound on the block clocks
or choice of an infinite sequence of blocks is assumed.

These formal units use `Core`'s finite-support `List Int` tapes, including
arbitrary list representations. The submitted ordinary proof has the broader
all-function-tapes formulation. Neither claim should be silently substituted
for the other. Blank tape is within the checked formal domain.

Each guard reuses exactly two selected project source/object pairs from the
actual checked BinaryRouting245 evidence. It pins the compiler and relevant
toolchain providers, captures the newly compiled object before auditing, and
checks inputs and first providers afterwards. Source and audit share 120 seconds,
run serially with `-j1 -M4096`, and use default proof limits. No dependency
build, download, compiler-version query, `sorry` or `native_decide` is used.
This does not re-execute the 851-module ancestor closure.

The generic first attempt remains a failed whole-unit check: both Lean commands
succeeded, but an unqualified audit name also printed an imported theorem,
producing five reports instead of four. Fully qualifying the four audit names
repaired the census; the source and typed callers were unchanged. Original
logs, failed record, earlier unexecuted drafts, repairs, exact guards and review
receipts are retained under [compensated244-formal](compensated244-formal/).
Review roles are stated in the receipts, including the invariant author's
review of the root's execution. The source's historical draft comment is
preserved; the actual execution record establishes its later checked status.

## Reproduction

From this directory, run one unit at a time with a new external output directory:

```sh
python3 -B check_positive_block_bisimulation.py --prepare-only --output /tmp/c244-generic-prepared
python3 -B check_positive_block_bisimulation.py --output /tmp/c244-generic-actual
python3 -B check_routing245_invariant.py --output /tmp/c244-invariant-actual
python3 -B check_table_compensated244.py --output /tmp/c244-table-actual
```

The maintained guards differ from the executed guards only in source, audit
and boundary path defaults; the exact changes are retained as publication
diffs. They require the exact existing cached providers and compiler named
in their boundaries, including historical scratch paths. Preparation invokes
no proof compiler. This is a check against recorded providers, not a standalone
dependency bootstrap for a fresh machine.

The remaining transfer obligations are the seven local execution blocks,
their global checkpoint simulation, and composition with
[BinaryRouting245](routing245_binary.md). Internal PA formalization remains
a separate open task. No absolute consistency or unconditional nonhalting
claim follows from these three units.
