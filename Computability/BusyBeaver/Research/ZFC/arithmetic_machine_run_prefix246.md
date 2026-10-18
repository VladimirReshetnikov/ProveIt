# Exact 246-state arithmetic run

`ArithmeticMachineRunPrefix246` gives one fixed Σ₁ run graph, with a Δ₁ definition of the same function, for the canonical 246-state machine. Foundation's primitive-recursion construction proves total unique evaluation at every internal time in every IΣ₁ model. A separate induction proves that its interpretation over the ordinary natural numbers agrees with the complete numeric machine run at every time, without a cutoff.

The initial configuration is code 1, the actual blank tape in canonical state 0. The successor clause applies the fixed exact246 step graph. The source also defines a closed parameter-free Σ₁ halting sentence and proves that its ordinary-natural interpretation is exactly blank-tape halting of `machinePrefix246`. It proves a closed totality sentence in IΣ₁ and hence PA.

The source and audit passed on the first actual attempt. The earlier guard with a pending Step parent and the exact change to the successful Step record remain in the history. No theorem or proof-limit changes were made when freezing that parent.

Totality at internal times and agreement with ordinary-natural machine runs are distinct conclusions. This unit does not yet compare arbitrary internal runs with the register interpreter or prove a PA consistency equivalence. The [finite bootstrap](arithmetic_bootstrap_prefix246.md) transports the checked concrete startup into the same graph.

The [successful record](results/arithmetic-machine-run-prefix246-verification.json) contains 14 named axiom probes and 16 typed callers, all using only standard Lean axioms. The final source and audit took 4.074 and 2.095 seconds, with no warnings. The fresh source object was recorded before the audit and remained unchanged afterward.

The [independent review](results/arithmetic-machine-run-prefix246-review.json) rehashed all 73 current inputs and checked the actual first object providers. The exact import traversal selects 26 project modules and 3 direct Foundation/Mathlib cache boundaries. Generic arithmetic helpers located in earlier Perm252 modules retain their original names; the concrete table and the new arithmetic definitions are the 246-state ones. The [history](results/arithmetic-machine-run-prefix246-history.json) retains exact records, source/audit snapshots, logs, executed guards and development evidence.

The portable guard defaults to this maintained source, audit, the published MP254 evidence, and the exact [step record](results/arithmetic-machine-step-prefix246-verification.json). Its control flow and proof checks match the executed guard; only default path resolution changes. Successful records retain their actual historical source and object paths, including scratch cache providers. Publication does not supply or rebuild those objects. Reproduction therefore requires those exact recorded provider bytes to remain available.

With those prerequisites available, run preparation from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_machine_run_prefix246.py \
  --repo "$PWD" \
  --output /tmp/zfc-arithmetic-machine-run-prefix246-prepared \
  --prepare-only
```

Preparation performs no compiler or compiler-version query. Omitting `--prepare-only` checks only the source and audit with one thread, 4,096 MiB and a shared 120-second bound; the new proofs use default Lean proof limits. Dependencies are reused without a build or download. The guard preserves explicit historical provider paths rather than claiming that this cache-dependent recipe is a clean checkout build.

Attribution follows the canonical table: Mira-Cult's original machine and calculus, Jeff Ketchersid's verification, Andrew James Wade's compiler framework, and source63's contextual reduction.
