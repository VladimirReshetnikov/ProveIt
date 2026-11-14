# The 198-state source-pruning runtime experiment

**This is not an accepted blank-tape consistency machine and not a sub-196 construction.**
It is an experimental 198-working-state binary table whose instruction contracts
hold from the supplied source frames. Its blank startup has not been calibrated.

The source removes the always-zero register-6 test at ordinal 7 of the published
PA196 program and its unreachable positive-loop body (old ordinal 8). In the
binary syntax tree, replace the subtree at address `00011` by its right child.
The new source has 3,810 instruction occurrences and 4,956 branch contracts.
The table uses native labels, starts in 74 on blank tape, dispatches source
instructions in 84, and halts at the undefined terminal label 254. There are
198 working labels and 396 transition rows; the sparse magnitude of a label is
not the number of states.

## Reproduce the arbitrary-natural runtime check

Python 3.10 or later, standard library only. From this directory run:

```sh
python3 check_pruned.py
```

This takes approximately two minutes and writes `runtime_receipt.json`. The
expected status is `ARBITRARY_NATURAL_PRIMITIVE_CONTRACTS_PASS`, with 4,956
contracts. Each frame has a gap of `56+n` for an arbitrary natural number `n`,
nine arbitrary natural registers (conditioned on the selected decrement branch),
and an arbitrary nonempty spare-register list. The checker proves its four
list-traversal block schemas from the actual table, then checks complete tape
endpoints. This is executable mathematical evidence using the inherited
unary/list engine; it is **not a Lean kernel certificate**.

Assertions must be enabled. The engine refuses Python `-O` and `PYTHONOPTIMIZE`.
Input and engine hashes are checked against `manifest.json` before replay.

## Reproduce the startup limitation

```sh
python3 check_startup.py
```

The script first reproduces the published baseline's 58,154-step clean seed
using the included unchanged baseline native table. It then runs the experimental
198-state table on blank tape for 1,000,000 literal steps. The supplied receipt
records that neither the original clean seed nor a decoded candidate-2 source
frame was found within that bound. It writes `startup_receipt.json`.

This is a bounded negative result, not a proof that a clean seed never occurs.
No equivalence with `Con(PA)` from blank tape is asserted for this table. Even
a successful source-level pruning and universal instruction contracts leave a
separate blank-startup obligation. The state count also exceeds the requested
maximum of 195.

## Contents and provenance

- `data/runtime_198.native.tm`, `data/runtime_198.sites.json`: the experimental
  table and its full source-address list.
- `data/pa196_baseline.native.tm`: the published 196-state table converted
  through its exact upstream conjugacy labels, for the startup reference.
- `native_symbolic.py`, `source_ops.py`: the inherited mathematical checker
  from ProveIt's `u208_research_2026-10-29` archive, specifically
  `baseline_evidence/compatibility/code/runtime`. Only the leading documentation
  of `native_symbolic.py` was adapted to identify its provenance here.
- `check_pruned.py`, `check_startup.py`: portable wrappers written for this
  packet. They do not import files outside this directory.
- `search_receipt.json`: classification of related searches and rejected
  allocations. The remaining rejected tables are not included here.
- `licenses/`: retained source-lineage license and attribution notices.

Pinned BusyBeaver revision: `407cdc356f6b586635e71ac92be394255f4bfea4`.
Pinned ProveIt revision: `f7d2482e35cf2f8f3bd03b5a82387ad999243548`.
The complete comparison elsewhere in the archive documents the untouched
baseline's publication identity. The supplied license notices remain applicable;
no blanket relicensing of inherited material is asserted.
