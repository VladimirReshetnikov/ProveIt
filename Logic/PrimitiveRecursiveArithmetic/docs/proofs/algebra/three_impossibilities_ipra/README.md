# Three classical construction impossibilities in iPRA

This archive contains a constructive proof architecture for:

1. impossibility of doubling the unit cube by straightedge and compass;
2. impossibility of trisecting the constructible 60-degree angle by straightedge and compass;
3. impossibility of squaring the unit circle by straightedge and compass.

The intended foundational target is intuitionistic primitive recursive arithmetic (`iPRA`), using the existing `ProveIt/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA` syntax, derivability relation, quantifier-free induction theorem, and native/ordinary bi-interpretation.

## Main files

- `three_classical_impossibilities_ipra.pdf` - 28-page human-readable proof and Lean roadmap.
- `three_classical_impossibilities_ipra.tex` - LaTeX source.
- `formalization/IPRAFormalizationBlueprint.lean` - compile-oriented dependency mock. It deliberately exposes unfinished milestone lemmas as axioms; it is not the completed formalization.
- `formalization/ModuleMap.md` - implementation plan and completion criteria.
- `scripts/finite_checks.py` - dependency-free exact checks of selected algebraic identities, Hermite divisibility formulas, and the explicit factorial threshold.
- `evidence/finite_checks.txt` - output of the check script.
- `CLAIMS.md` - precise status and trust-boundary statement.
- `provenance/SOURCES.md` - pinned source revisions and files consulted.
- `SHA256SUMS` - checksums of the deliverable files.

## Build

```bash
latexmk -pdf -interaction=nonstopmode \
  -outdir=build three_classical_impossibilities_ipra.tex
cp build/three_classical_impossibilities_ipra.pdf .
python3 scripts/finite_checks.py
```

The PDF was rendered page-by-page and visually inspected after compilation.

## Logical scope

The paper gives the ordinary constructive mathematics in enough detail to identify the primitive-recursive programs and bounds required by an object-level proof. It does **not** claim that the full `PRAAx` derivation has already been implemented. The two cubic arguments are close to direct formalization. The largest remaining formalization component is certified complex-root isolation integrated with the coded real/complex approximation library used by the finite Hermite-Lindemann argument.
