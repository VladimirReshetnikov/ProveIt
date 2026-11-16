# STRIVE-iPRA

**Strategy-Table Realization with Interface Verification and Elimination**

This research packet develops a kernel-facing framework for translating fixed,
finite mathematical interactions into ordinary intuitionistic primitive recursive
arithmetic (`Prf PRAAx`). It was prepared against
`VladimirReshetnikov/ProveIt` commit
`58627ed89814ba122e1f0f012f1aba103cda267b` on 2026-11-16.

## Main contribution

STRIVE makes the variable-length certificates used in earlier bounded-game and
finite-interaction frameworks explicit. For every fixed bounded formula it gives:

- heterogeneous mixed-radix bounds for positive and negative strategy tables;
- a canonical least strategy code and a primitive-recursive checker;
- separate object-theory soundness theorems for success and failure;
- certificate escape analysis: erase local certificates, observe noncanonical
  certificates, and name a certificate only when the public theorem requires it;
- exact residual formulas for missing height bounds, moduli, separation data,
  finite-cover certificates, or other genuine producers;
- a dependency-ordered path to Lean theorems of the literal form
  `Prf PRAAx Γ φ`, followed only afterwards by optional bridge/native exports.

The report also integrates finite demand closure, relational viability, stable
observers, and open-sequent transport already present in the repository. Those
ingredients are credited as inherited rather than claimed as new.

## Verification status

- Human mathematical proofs: developed in `paper/strive_ipra_framework.pdf`.
- Python reference implementation: tested; it implements the exact signed
  strategy-code recursion, checker, mixed-radix operations, and demand closure.
- Lean: `lean/STRIVE/Kernel.lean` is a small source-compatible structural
  candidate without placeholders; the larger files are explicit blueprints
  containing `sorry` milestones. Lean was not available in this runtime, so no
  new kernel-checked theorem is claimed.
- The packet does **not** manufacture missing global height bounds, convergence
  moduli, compactness data, or branch-separation resources. Such inputs remain
  visible residual contracts.

## Contents

- `paper/strive_ipra_framework.tex` and `.pdf` - complete report.
- `lean/STRIVE/` - structural kernel and dependency-ordered Lean blueprints.
- `lean/FORMALIZATION_PLAN.md` - exact integration route.
- `reference/strive_reference.py` - executable reference algorithms.
- `reference/test_strive_reference.py` - regression and exhaustive small-model tests.
- `reference/generate_examples.py` - regenerates JSON examples.
- `examples/` - success, failure, empty-bound, and cyclic-demand examples.
- `metadata/` - theorem ledger, difficulty matrix, provenance, and claims.
- `validation/` - build/test/render receipts.

## Reproduce

```bash
bash build.sh
```

This runs the Python tests, regenerates examples, and compiles the PDF. Lean
integration requires a checkout of the pinned ProveIt repository and the steps
in `lean/FORMALIZATION_PLAN.md`.
