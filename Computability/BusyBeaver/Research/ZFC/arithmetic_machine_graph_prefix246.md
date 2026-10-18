# Exact 246-state arithmetic transition lookup

`ArithmeticMachineGraphPrefix246` gives a fixed bounded arithmetic formula for the exact 246-state machine's transition lookup. Its rows are derived directly from the imported canonical table. A checked finite theorem identifies every one of the 492 actions with the typed machine, and the formula defines a total function in every IOpen model.

Source-state keys are canonical state plus one. An absent source key returns zero; a zero read-bit selects the first action and any nonzero read-bit selects the second. Actual machine bits are zero or one. Real actions are encoded positively: the terminal write-one/right action is code 4, while the initial read-zero action is code 408. A real halt therefore retains its write and movement. The reusable upper bound is 1,012; the actual table's action codes range from 4 through 988.

The [successful record](results/arithmetic-machine-graph-prefix246-verification.json) passed eight named axiom probes and eight typed callers, with no warnings. Source and audit took 10.728 seconds and 1.707 seconds. Three probes have no axioms, two use `propext`, and the three generic arithmetic graph probes use only `propext`, `Classical.choice` and `Quot.sound`. The source object was recorded before the audit and remained unchanged afterward.

The guard selects exactly 23 project imports from the successful MP254 and TablePrefix246 records, plus three explicit cached Foundation/Mathlib boundaries and Init/Omega. It excludes the unrelated MP runtime modules and historical alternative objects. All 68 inputs, actual first providers, proof snapshots and fresh object were rechecked in the [independent source and evidence review](results/arithmetic-machine-graph-prefix246-review.json). The fixed graph reuses generic declarations housed in Perm252 modules; it instantiates their table parameter with the exact 246 table.

[History](results/arithmetic-machine-graph-prefix246-history.json) preserves the sole actual source/audit attempt, exact record, logs, executed guard, snapshots, and prior source reviews. Publication preserves the successful proof bytes. The portable guard changes only default paths for the source, audit and exact TablePrefix246 parent record; the successful record keeps its actual scratch table-evidence path. No proof replay occurs during publication.

With the exact recorded provider objects still available:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_machine_graph_prefix246.py \
  --repo "$PWD" \
  --output /tmp/zfc-arithmetic-graph-prefix246-prepared \
  --prepare-only
```

The maintained defaults use the published MP254 and TablePrefix246 records. Preparation performs no compiler or version query. Removing `--prepare-only` checks only this source and audit, sharing 120 seconds with one thread, 4,096 MiB and default limits for the new proofs. Dependency objects are reused without a build or download.

This unit closes the fixed arithmetic action lookup. Internal step iteration, the numeric whole-tape run, startup, runtime simulation and the PA consistency equivalence remain separate obligations. Attribution follows the canonical table: Mira-Cult's original machine and calculus, Jeff Ketchersid's verification, Andrew James Wade's compiler framework, and source63's contextual reduction.
