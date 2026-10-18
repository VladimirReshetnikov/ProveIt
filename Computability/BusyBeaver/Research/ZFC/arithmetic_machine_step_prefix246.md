# Exact 246-state arithmetic step

`ArithmeticMachineStepPrefix246` defines one fixed bounded arithmetic step graph using the canonical 246-state transition lookup. It is total and unique at every input of every IOpen model. On ordinary natural configuration codes it agrees with the actual machine's numeric step, including both tape halves.

State code zero represents a halted configuration. Codes above 246 are invalid; both kinds remain unchanged. Actual terminal actions still write and move before setting the state to zero. The audit checks the concrete old77/canonical71 terminal transition, which changes `⟨72,l,2*r+1⟩` to `⟨0,2*l+1,r⟩`.

The source was unchanged throughout three attempts. Runs 1 and 2 each checked the source successfully but failed a typed audit caller: first an unmatched `Fin` presentation, then the remaining identity `(2*r+1)/2=r`. Run 3 supplies the numeral form and an `omega` proof of that identity. The original warning in run 1, both failures, and the earlier preparation with the original audit remain in the history. The final source and audit have no warnings.

This unit supplies the local arithmetic step. The [run graph](arithmetic_machine_run_prefix246.md) and [finite bootstrap](arithmetic_bootstrap_prefix246.md) build on it; an internal comparison with the register interpreter and the PA consistency equivalence remain separate.

The [successful record](results/arithmetic-machine-step-prefix246-verification.json) contains 7 named axiom probes and 10 typed callers, all using only standard Lean axioms. The final source and audit took 2.319 and 1.793 seconds, with no warnings. The fresh source object was recorded before the audit and remained unchanged afterward.

The [independent review](results/arithmetic-machine-step-prefix246-review.json) rehashed all 71 current inputs and checked the actual first object providers. The exact import traversal selects 25 project modules and 3 direct Foundation/Mathlib cache boundaries. Generic arithmetic helpers located in earlier Perm252 modules retain their original names; the concrete table and the new arithmetic definitions are the 246-state ones. The [history](results/arithmetic-machine-step-prefix246-history.json) retains exact records, source/audit snapshots, logs, executed guards and development evidence.

The portable guard defaults to this maintained source, audit, the published MP254 evidence, and the exact [graph record](results/arithmetic-machine-graph-prefix246-verification.json). Its control flow and proof checks match the executed guard; only default path resolution changes. Successful records retain their actual historical source and object paths, including scratch cache providers. Publication does not supply or rebuild those objects. Reproduction therefore requires those exact recorded provider bytes to remain available.

With those prerequisites available, run preparation from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_machine_step_prefix246.py \
  --repo "$PWD" \
  --output /tmp/zfc-arithmetic-machine-step-prefix246-prepared \
  --prepare-only
```

Preparation performs no compiler or compiler-version query. Omitting `--prepare-only` checks only the source and audit with one thread, 4,096 MiB and a shared 120-second bound; the new proofs use default Lean proof limits. Dependencies are reused without a build or download. The guard preserves explicit historical provider paths rather than claiming that this cache-dependent recipe is a clean checkout build.

Attribution follows the canonical table: Mira-Cult's original machine and calculus, Jeff Ketchersid's verification, Andrew James Wade's compiler framework, and source63's contextual reduction.
