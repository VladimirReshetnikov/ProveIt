# Conditional runtime equivalence for prefix246

`RuntimeInstancePrefix246.lean` proves both directions of halting equivalence between the logical register program and the exact 246-state machine, given complete accepted site coverage and an initial related dispatch frame. The relation retains a clean program counter, the whole physical tape and an explicitly nonempty finite spare suffix.

Every logical step becomes a strictly positive binary segment and preserves that relation. Increment appends a value-one spare; other instructions retain the suffix. Coverage is used explicitly to distinguish a genuine halt leaf from a failed decode. The generic `PositiveSimulation` theorem supplies the two halting directions by finite induction, without an additional fairness premise.

Root's first source/audit run passed: 11 named axiom probes and 12 typed callers, standard Lean axioms only, zero warnings. Source took 0.621 seconds and audit 0.477 seconds. The guard uses one thread, 4,096 MiB, a shared 120-second budget and default proof limits, with no dependency builds or version query. Final evidence review rechecked all 71 recorded inputs, the complete 26-project import closure, Init/Omega boundaries, actual first providers and the fresh source object recorded before audit.

The sole successful attempt and raw snapshots are retained; the history archive was assembled after success from those exact bytes. Publication changes only the guard's source/audit default paths.

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_prefix246_runtime.py \
  --repo "$PWD" \
  --instruction-evidence Computability/BusyBeaver/Research/ZFC/results/prefix246-instruction-verification.json \
  --output /tmp/zfc-prefix246-runtime-check --prepare-only
```

Use a new external output directory. Preparation invokes no compiler or version query; removing `--prepare-only` requests the bounded source/audit run. The successful record retains the actual scratch Instruction evidence path used during that run; the identical maintained record is accepted above.

This module keeps `Covered` or a closed `allSites` theorem and the initial `Related` frame as explicit premises. It does not supply actual-tree coverage, the blank-tape bootstrap, a binary consistency theorem or PA internalization. Attribution follows the checked 250-state port and the Mira-Cult, Jeff Ketchersid and Wade runtime framework.
