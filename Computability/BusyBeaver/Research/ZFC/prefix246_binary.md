# Exact 246-state blank machine: external ZF/ZFC calibration

The checked [BinaryPrefix246 source](../../Lean/BusyBeaver/ZFC/BinaryPrefix246.lean) proves that the literal canonical 246-state machine, started in state 0 at head 0 on the empty binary tape, halts exactly when there is a `BProv` refutation of ZF, and exactly when there is a `BProv` refutation of the repository's ZFC axioms. Negating those equivalences gives `nonhalting_iff_zf_consistency` and `nonhalting_iff_zfc_consistency`.

These are closed external Lean theorems. No runtime-coverage or startup hypothesis remains in their statements. They are not object-language PA proofs, and they assert neither unconditional consistency nor unconditional nonhalting. The original PA-provability goal remains tracked in [PA internalization](pa_internalization.md).

The proof joins the complete 8,391 decoder cases for the actual program, the checked 410,735-step startup including the entire tape, the nonempty spare suffix, the whole-frame runtime simulation, and the independently calibrated logical seed. A generic finite-prefix argument also covers a halt inside the prefix by halt absorption. The exact [candidate and transition table](candidate-prefix246/README.md), [coverage](prefix246_coverage.md), [bootstrap frame](prefix246_bootstrap_frame.md), [runtime](prefix246_runtime.md), and [logical seed](logical_seed246.md) retain their separate evidence.

The [successful record](results/prefix246-binary-verification.json) passes nine named axiom probes and nine typed callers. The initial-configuration theorem uses no axioms; four probes use `propext` and `Quot.sound`; the four ZF/ZFC refutation and consistency probes also use `Classical.choice`. Source and audit took 0.499 and 0.474 seconds, with no warnings. The new source object was recorded before the audit and remained unchanged afterward.

The [history](results/prefix246-binary-history.json) preserves the original uncompiled reviews and publication plan, pending-parent guard, exact parent-pin transition, successful source/audit snapshots, logs and raw record. Later [independent evidence review](results/prefix246-binary-review.json) has its own explicit scope. The guard selects exactly 230 project prerequisites, including all 102 generated coverage modules. It pins 474 current inputs and checks their actual first object providers. This closure has no external project-cache boundary; toolchain providers remain explicit prerequisites.

The portable guard changes only the source and audit default locations. Its three parent-record arguments remain required. With the exact recorded compiler and historical provider objects available, prepare from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_binary_prefix246.py \
  --repo "$PWD" \
  --runtime-evidence "$PWD/Computability/BusyBeaver/Research/ZFC/results/prefix246-runtime-verification.json" \
  --bootstrap-evidence "$PWD/Computability/BusyBeaver/Research/ZFC/results/prefix246-bootstrap-frame-verification.json" \
  --coverage-evidence "$PWD/Computability/BusyBeaver/Research/ZFC/results/prefix246-sites-verification.json" \
  --output /tmp/zfc-prefix246-binary-prepared \
  --prepare-only
```

Preparation makes no compiler or version query. Removing `--prepare-only` checks just this source and audit using one thread, 4,096 MiB, a shared 120-second bound and default new-source proof limits. No dependency build or download occurs. Historical source/object paths inside successful records remain unchanged; the packet does not redistribute cached objects or claim a clean-checkout build.

Attribution follows Mira-Cult's original proof-search machine and calculus, Jeff Ketchersid's verification, Andrew James Wade's compiler framework, and source63's contextual reduction. The proof uses the exact canonical 246-state table already recorded for that candidate.
