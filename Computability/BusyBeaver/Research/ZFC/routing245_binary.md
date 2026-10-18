# Exact 245-state blank machine: external ZF/ZFC calibration

The checked [BinaryRouting245 source](../../Lean/BusyBeaver/ZFC/BinaryRouting245.lean) proves that the literal [245-state machine](candidate-routing245/README.md), started in state 0 at head 0 on the empty binary tape, halts exactly when there is a `BProv` refutation of ZF, and exactly when there is a `BProv` refutation of the repository's ZFC axioms. Negating these equivalences gives `nonhalting_iff_zf_consistency` and `nonhalting_iff_zfc_consistency`.

These are closed external Lean theorems. No runtime-coverage, startup or source-bisimulation hypothesis remains in their statements. They are not object-language PA proofs and assert neither unconditional consistency nor unconditional nonhalting. The remaining PA proof obligation is tracked in [PA internalization](pa_internalization.md).

The proof joins all 8,391 decoder guard cases of the actual routed program, the complete 407,915-step [blank startup](routing245_bootstrap.md), the nonempty spare suffix, the [whole-frame runtime simulation](routing245_execution.md), and the [3,013-pair source bisimulation](bisim_routing245.md) at the calibrated [logical seed](logical_seed246.md). The source bisimulation relates the routed and original programs at the same register function and empty pointer. A finite-prefix lemma accounts for a halt inside the startup prefix through halt absorption.

The [successful record](results/routing245-binary-verification.json) passes eleven named axiom probes and eleven typed callers, with zero warnings. Source and audit took 1.934654 and 0.527076 seconds. The exact axiom sets are retained in that record; every reported axiom belongs to `propext`, `Classical.choice` or `Quot.sound`. The fresh source object was captured as the first provider before audit and remained unchanged afterward. The [independent existing-evidence review](results/routing245-binary-review.json) states its scope separately. The first actual attempt passed the unchanged source but failed four audit callers because `BProv` was outside the opened namespaces. The successor adds only `SetTheory` to the audit’s `open` declaration; all theorem statements, probes and typed caller statements are unchanged. The complete second source/audit attempt passed. Both attempts, their raw outputs and both preparations remain in the history.

The guard selects exactly 851 project prerequisites, no external project boundary, and two explicit toolchain objects (`Init` and `Lean.Elab.Tactic.Omega`). It checked 1,726 current inputs and their actual first providers. The [parent-freeze and audit-repair records](results/routing245-binary-parent-freeze.json) identify the same four successful runtime, bootstrap-frame, complete-coverage and bisimulation parents. This wrapper retains the original freeze with its original audit and the separate successor freeze with the repaired audit; both original record byte strings are preserved in the history. The [history](results/routing245-binary-history.json) preserves the original pending and frame-pinned guards, helper draft correction and readiness, source reviews, actual parent freeze, preparations, every available endpoint attempt and its raw logs, and the exact reviewer support files. Earlier histories remain as recorded; no missing execution record or unavailable draft is reconstructed.

The portable guard changes only the source and audit default locations. All parent evidence pins and paths remain unchanged. With the exact historical compiler and provider caches available, preparation from the repository root is:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_binary_routing245.py \
  --repo "$PWD" \
  --output /tmp/zfc-routing245-binary-prepared \
  --prepare-only
```

The four parent-evidence options can select byte-identical copies of the pinned records. Preparation makes no compiler or version query. Removing `--prepare-only` checks only this source and audit with one thread, 4,096 MiB, a shared 120-second bound and default proof limits. No dependency build or download occurs. This publication does not redistribute compiled objects or provide a clean-checkout build; exact historical cached providers are prerequisites. Maintained-default preparation is recorded separately after installation.

Attribution follows Mira-Cult's original proof-search program and calculus, Jeff Ketchersid's verification, Andrew James Wade's compiler framework, and the routing245 reduction supplied in source 68. The [candidate page](candidate-routing245/README.md) retains the exact transition table and report provenance.
