# Scoped Certificate Realization for iPRA

This archive develops a general proof-producing interface between finitary
mathematics and the canonical ProveIt judgment `Prf PRAAx Γ φ`.

The central contribution is **certificate escape analysis**:

- proof-local certificates are eliminated by ordinary existential elimination;
- only certificate-independent observations escape from noncanonical data;
- bounded least search is used only when a certificate or canonical code must
  be named in the public result.

This refines the repository's earlier FQNF, CBIP, observation-graph, and native
clause frameworks. It gives fully developed human arguments for the generic composition, trace,
strategy, observer, and boundary theorems; a no-placeholder Lean source
candidate for the small structural kernel; detailed Lean target signatures;
and exact reference programs with regression tests.

## Baseline

Repository: `VladimirReshetnikov/ProveIt`

Pinned commit: `f444b76e8480ebea128c15b4a59f158e14f478cc`
(2026-11-16 19:44:47 UTC).

## Main files

- `paper/scr_ipra_framework.pdf` — 48-page report.
- `paper/scr_ipra_framework.tex` and `paper/sections/` — editable LaTeX.
- `lean/ScopedCertificate/Kernel.lean` — no-placeholder structural kernel
  candidate using `Prf.exE`, `Prf.trans`, `Prf.subst`, and `Prf.weaken`.
- `lean/FORMALIZATION_PLAN.md` — dependency-ordered path to a complete Lean
  development and open-sequent bridge.
- `reference/scr_reference.py` — exact reference algorithms.
- `reference/test_scr_reference.py` — eight tests, executed successfully.
- `examples/demo.json` — generated evidence.
- `metadata/` — theorem ledger, difficulty matrix, source audit, and claims.
- `schema/scr_program.schema.json` — machine-readable metadata schema.

## Formal status

The generic mathematics is fully argued in the report. The Lean structural
kernel was not elaborated in the artifact runtime because no Lean executable
was installed. The archive therefore claims no new kernel-checked theorem.
The larger Lean development is explicitly a blueprint, not a formal proof.
Python tests are finite executable evidence only.

## Reproduce

```bash
bash build.sh
```

This runs the Python tests, regenerates `examples/demo.json`, and recompiles the
PDF. Lean integration requires a checkout of the pinned ProveIt repository;
follow `lean/FORMALIZATION_PLAN.md`.
