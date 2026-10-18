# Exact 246-state arithmetic bootstrap

`ArithmeticBootstrapPrefix246` transports the checked 410,735-step whole-tape startup of the canonical 246-state machine into its fixed arithmetic run graph. The startup target includes the complete numeric tape code, not only the control state or head position. `standard_boot` uses the exact `BootPrefix246Chunk008.bootstrap410735` theorem and generic numeric zipper uniqueness.

`run_cast` proves that at each external natural time, the represented run has the corresponding numeral value in every IΣ₁ model. Its proof uses the fixed Σ₁ functional graph and Foundation's absoluteness theorem. Applying this at 410,735 yields `internal_boot`. A literal closed Σ₁ startup sentence is then proved in IΣ₁ and PA.

The source and audit passed on the first actual attempt. The earlier guard with a pending Run parent and its exact successful-parent freeze remain in the history. The proof source, audit and proof limits were unchanged.

The cast theorem quantifies over external natural times; it does not assert comparison with the register interpreter at arbitrary internal times. The unit closes the finite arithmetic startup obligation. The unbounded internal simulation and PA consistency equivalence remain separate.

The [successful record](results/arithmetic-bootstrap-prefix246-verification.json) contains 7 named axiom probes and 9 typed callers, all using only standard Lean axioms. The final source and audit took 2.175 and 2.002 seconds, with no warnings. The fresh source object was recorded before the audit and remained unchanged afterward.

The [independent review](results/arithmetic-bootstrap-prefix246-review.json) rehashed all 109 current inputs and checked the actual first object providers. The exact import traversal selects 41 project modules and 4 direct Foundation/Mathlib cache boundaries. Generic arithmetic helpers located in earlier Perm252 modules retain their original names; the concrete table and the new arithmetic definitions are the 246-state ones. The [history](results/arithmetic-bootstrap-prefix246-history.json) retains exact records, source/audit snapshots, logs, executed guards and development evidence.

The portable guard defaults to this maintained source, audit, the published MP254 evidence, and the exact [run record](results/arithmetic-machine-run-prefix246-verification.json), [bootstrap record](bootstrap-prefix246/attempts/group08/run1/verification.json). Its control flow and proof checks match the executed guard; only default path resolution changes. Successful records retain their actual historical source and object paths, including scratch cache providers. Publication does not supply or rebuild those objects. Reproduction therefore requires those exact recorded provider bytes to remain available.

With those prerequisites available, run preparation from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_bootstrap_prefix246.py \
  --repo "$PWD" \
  --output /tmp/zfc-arithmetic-bootstrap-prefix246-prepared \
  --prepare-only
```

Preparation performs no compiler or compiler-version query. Omitting `--prepare-only` checks only the source and audit with one thread, 4,096 MiB and a shared 120-second bound; the new proofs use default Lean proof limits. Dependencies are reused without a build or download. The guard preserves explicit historical provider paths rather than claiming that this cache-dependent recipe is a clean checkout build.

Attribution follows the canonical table: Mira-Cult's original machine and calculus, Jeff Ketchersid's verification, Andrew James Wade's compiler framework, and source63's contextual reduction.
