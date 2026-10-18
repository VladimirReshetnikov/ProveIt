# Balanced lookup for the exact 246-state table

[FastTablePrefix246.lean](../../Lean/BusyBeaver/ZFC/FastTablePrefix246.lean) defines a balanced transition tree for the exact [246-state candidate](candidate-prefix246/README.md). Lean checks equality with the canonical machine on all 492 actions and then proves equality of the complete machine values. Finite computations can use the tree lookup and transfer their results to `machinePrefix246` through that equality.

The two theorems are `fast_transition_eq` and `fastMachine_eq`. The first has no axiom dependencies; the second uses only standard `Quot.sound` through function extensionality. The source and audit passed on their first run in 5.203 and 0.240 seconds, with two ordered axiom probes, four client examples and zero warnings. The finite action equality uses trusted `decide +kernel` under default proof limits.

The [exact verification record](results/fast-table-prefix246-verification.json) has SHA-256 `e048c1f6dfca04de875e48344e2c4f2a4fb4d2d0ea7562c87f23f4cd433ba850`. Source SHA-256 is `dec5303498f4ae17469e8ef79d684f3aaffd959e37a10880261cc200f602e031`; the fresh object is `d0f3525f29c577509e3404a71ba77b3958d3496927c7b8a25fb08d40d1d15b04`. The [history and independent review](results/fast-table-prefix246-history.json) preserve the executed source, audit, guard, generator and logs. Archival copies were made after PASS and checked against the original before/after hashes and source/audit snapshots.

The check reuses only exact checked `Core` and `TablePrefix246` objects plus the pinned implicit `Init` toolchain provider. It performs no dependency build, download or compiler-version query. Source and audit run serially with `-j1 -M4096`, one shared 120-second budget and unchanged proof limits. The guard records the fresh object before the audit and verifies input, provider and object hashes afterwards.

## Reproduction

From this directory, use fresh external output directories:

```sh
python3 -B generate_fast_prefix246.py --check
python3 -B check_fast_table_prefix246.py --output /tmp/prefix246-fast-prepared --prepare-only
python3 -B check_fast_table_prefix246.py --output /tmp/prefix246-fast-checked
```

The generator handles only the fast-table source. Its output remains an untrusted input until Lean checks the equalities. Preparation invokes no proof command. The full check requires the exact cached parent objects and compiler recorded in the evidence. Published source and audit are unchanged; publication changes only repository discovery and path defaults in the generator and guard. The [publication record](results/fast-table-prefix246-publication.json) and [maintained-default preparation](results/fast-table-prefix246-maintained-prepare.json) record those bindings.

This module establishes table equality. The 410,735-step startup, runtime simulation and consistency endpoint remain separate. The tree format follows the checked prefix250/BootPerm252 implementation, with every action generated anew from the exact246 canonical table. Attribution for the machine and contextual folds remains in the candidate and [table documentation](table_prefix246.md).
