# Kernel-Integrated Finitary Contracts for iPRA

This archive develops **KIFC**, a proof-producing framework for embedding
finitary mathematics into intuitionistic primitive recursive arithmetic.

## Main contribution

A fixed theorem-specific construction is normalized into six node classes:

1. exact algebra;
2. Boolean decision;
3. bounded search;
4. certified iteration;
5. finite relational choice;
6. stable or guarded observation.

A reverse pass fixes finite precision and resource demands. A forward pass is
specialized to one primitive-recursive state machine with a quantifier-free
invariant. Local embedded `Prf PRAAx` certificates are composed by substitution
and simultaneous cut. Non-unique witnesses are handled by finite backward
viability and stable observations; coherent infinite names are exported only
when shrinking and tail data are explicit.

## Contents

- `paper/ipra_kifc_framework.pdf` - compiled 50+ page report.
- `paper/ipra_kifc_framework.tex` and `paper/sections/*.tex` - LaTeX source.
- `lean/KIFC/*.lean` - kernel-facing core and source-oriented Lean blueprints.
- `lean/FORMALIZATION_PLAN.md` - dependency order and completion gates.
- `reference/kifc_reference.py` - exact finite reference implementation.
- `reference/test_kifc_reference.py` - 14 regression/property tests.
- `examples/*.json` - graph and relation examples.
- `metadata/THEOREM_LEDGER.md` - claim-by-claim status.
- `metadata/difficulty_matrix.csv` - obstacle/resolution audit.
- `metadata/SOURCE_AUDIT.md` - pinned repository sources.
- `validation/` - build, test, PDF, and render records.

## Status

- Human-readable mathematics: developed in the report.
- Python reference: 14 tests pass.
- PDF: compiled, preflighted, and visually audited in this artifact.
- Lean: source-oriented outline only; Lean was unavailable in the artifact
  environment, so no new-module compilation is claimed.
- Inherited ProveIt object theorems: inspected at repository snapshot
  `8649990597d73657bde480b6c389de7f85bc0cb0`.

## Reproduction

From the artifact root:

```sh
python3 -m unittest -v reference/test_kifc_reference.py
cd paper
pdflatex -interaction=nonstopmode -halt-on-error ipra_kifc_framework.tex
pdflatex -interaction=nonstopmode -halt-on-error ipra_kifc_framework.tex
```

The convenience script `build.sh` runs tests, rebuilds the PDF, preflights it,
and refreshes the manifest.
