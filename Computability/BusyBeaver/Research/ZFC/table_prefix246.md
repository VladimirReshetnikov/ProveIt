# Exact 246-state table in Lean

[TablePrefix246.lean](../../Lean/BusyBeaver/ZFC/TablePrefix246.lean) defines the exact [contextual-fold candidate](candidate-prefix246/README.md): 246 working states, 492 literal actions, blank start 0 (old95), dispatch 88 (old96), and numerical halt246. The final transition retains its write and movement. Both frozen table forms and their exact renumbering are checked by the source generator; the guard separately parses every emitted action against the canonical table.

Lean has checked47 named theorems and47 direct callers. They establish the table census and target bounds, unique halt action, old/canonical state inverse, exact incoming-edge characterizations, and29 literal row facts for the pulse and selector proofs. In particular, old255 has a read-zero self-loop: its incoming characterization includes both old75/read-zero and old255/read-zero. The absent old97 is not treated as a retained machine state. The total `oldStatePrefix246` function defaults to canonical0 for absent labels; its inverse theorem is stated only for the actual canonical state domain.

The source and audit passed on the first run in20.796 and0.345 seconds, with zero warnings. The first six axiom reports are empty; the remaining41 contain only standard `propext`. Finite facts use trusted `decide +kernel` under default proof limits. There is no additional proof axiom or native evaluation axiom.

The [exact PASS record](results/table-prefix246-verification.json) has SHA-256 `70a9a9bfb1546a1c0c6f1503c6261d2d23637dd901e7debec220e7185137ed6d`. Source SHA-256 is `cb2e5e91150fa40a864ecbe216c7c1c0d21a0bf70f8e9d78b3acdb2a0f046864`; the fresh object is `8bd0913d019d431d37fee9c5a32e7686052e92732e16e454ff4fce0bf56cc3ec`. The [history and independent review](results/table-prefix246-history.json) preserve the executed source, audit, guard, generator and logs. The archival copies were made after PASS and checked against the original before/after hashes; the original source and audit snapshots are also recorded.

Only one checked `BusyBeaver.Core` source/object pair is reused. The supplied compiler and implicit `Init` object are pinned. The guard performs no dependency build, download or compiler-version query. Both proof commands run serially with `-j1 -M4096` and one shared120-second source/audit budget. It persists the fresh source object before the audit and checks all inputs, providers and that object afterwards.

## Reproduction

From this directory:

```sh
python3 -B generate_table_prefix246.py --check
python3 -B check_table_prefix246.py --output /tmp/prefix246-table-prepared --prepare-only
python3 -B check_table_prefix246.py --output /tmp/prefix246-table-checked
```

Use fresh external output directories. Source generation and preparation execute no proof command. A full check requires the exact existing Core object and toolchain recorded in the parent evidence; it rejects changed providers. Published source and audit are byte-identical to the successful run. Generator and guard publication changes only repository discovery and path defaults. The [publication record](results/table-prefix246-publication.json) and [maintained-default preparation](results/table-prefix246-maintained-prepare.json) bind those paths to the checked evidence.

This unit establishes finite table facts. The410735-step blank startup, runtime representation, unbounded simulation, exact consistency endpoint and PA formalization remain separate obligations. Attribution for the original calculus, machine, compiler, earlier reductions and source63 contextual folds remains in the candidate documentation.
