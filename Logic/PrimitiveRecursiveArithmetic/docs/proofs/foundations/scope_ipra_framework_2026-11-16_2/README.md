# SCOPE-iPRA

**Scoped Observational Contracts and Proof Extraction** is a framework for
embedding finite mathematical observations and proofs into intuitionistic
primitive recursive arithmetic.

The report is pinned to ProveIt commit
`8dfe26af18310f58aaff695fb0ce03ff5007d096` (2026-11-16).

## Main contributions

- schema-first bounded reflection: a fixed bounded formula scheme compiles to a
  fixed `PR k` symbol, so substitution changes only its arguments;
- truth and falsity reflection for bounded formulas;
- certificate escape modes: sealed, relational, and named;
- scoped realization and relational observer theorems;
- a scope-minimal normal form for finite proof graphs;
- a proof-plan compiler whose intended endpoint is a literal `Prf PRAAx`;
- trace, cyclic demand, and whole-path viability modules;
- barrier-aware treatments of branch selection, metastability, compactness, and
  effective finiteness.

## Exact artifact status

- `paper/scope_ipra_framework.pdf`: compiled report.
- `paper/*.tex` and `paper/sections/*.tex`: complete editable source.
- `lean/SCOPE/Kernel.lean`: no-placeholder structural kernel candidate, matched
  to the pinned API but not elaborated in this runtime.
- `lean/SCOPE/BoundedCode.lean` and `CompilerBlueprint.lean`: definitions and
  exact target signatures; explicitly blueprints, not checked formalizations.
- `reference/`: executable semantic reference and 16 passing tests. These tests
  do **not** constitute object-iPRA proofs.
- `metadata/THEOREM_LEDGER.md`: claim-by-claim status.
- `validation/`: test output, static audit, PDF preflight, and a rendered contact sheet.
- `MANIFEST.txt`: plain relative file inventory (no checksum manifest).

The runtime used for this delivery had no `lean` or `lake` executable. The
formalization plan records a direct path to checked repository integration.

## Reproduce

```bash
python3 -m unittest -v reference/test_scope_reference.py
python3 reference/scope_reference.py --pretty > examples/demo.json
bash build.sh
```

`build.sh` runs the Python tests, compiles the PDF with `latexmk`, and checks
for unresolved references and LaTeX errors.
