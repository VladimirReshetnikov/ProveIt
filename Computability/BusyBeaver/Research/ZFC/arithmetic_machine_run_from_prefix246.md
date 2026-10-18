# Arbitrary-start arithmetic runs of the exact 246-state machine

`ArithmeticMachineRunFromPrefix246` defines a fixed Σ₁ graph, with a Δ₁ definition of the same function, for iteration from any arithmetic configuration code. Totality, addition of run times, and recovery of the blank evaluator hold for arbitrary internal initial codes and times in every IΣ₁ model. Halt absorption preserves the entire encoded configuration, including both tape halves.

The fixed step is the checked 246-state step. Generic lookup and tape-action helpers retain their existing Perm252 namespaces, while the literal rows, action lookup, native step and blank run are explicitly the 246 definitions. The source separately proves ordinary-natural agreement with native code iteration. It adds no comparison with the register interpreter or scheduler.

The direct port removes the original increased proof options. Its first source/audit attempt passed at default limits. The [prefix unit](arithmetic_machine_prefix_prefix246.md) uses these iteration laws to remove the checked startup from the internal halting condition.

The [successful record](results/arithmetic-machine-run-from-prefix246-verification.json) has 19 named axiom probes and 23 typed callers, with no warnings. Source and audit took 6.428 and 2.752 seconds. The fresh source object was recorded before its audit and remained unchanged afterward. The [history](results/arithmetic-machine-run-from-prefix246-history.json) retains the original preparation where present, source generation, pending-parent evidence, exact proof snapshots, logs and reviews. Initial unbuilt reviews retain their original scope alongside the later [independent evidence review](results/arithmetic-machine-run-from-prefix246-review.json).

The guard selects exactly 27 prerequisite project modules and 3 direct Foundation/Mathlib boundaries, with 75 pinned inputs. The portable copy changes only source/audit/parent default paths. Successful records retain actual historical source and object paths. These cache-dependent prerequisites are not rebuilt or redistributed by the packet.

With the exact recorded provider bytes available, prepare from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_machine_run_from_prefix246.py \
  --repo "$PWD" \
  --output /tmp/zfc-arithmetic-machine-run-from-prefix246-prepared \
  --prepare-only
```

Preparation performs no compiler or version query. Omitting `--prepare-only` checks only this source and audit with one thread, 4,096 MiB, a shared 120-second bound and default new-source proof limits. It performs no dependency build or download and does not claim a clean-checkout build. Attribution follows Mira-Cult's original machine/calculus, Jeff Ketchersid's verification, Andrew James Wade's compiler framework and source63's contextual reduction.
