# Source provenance

## Mathematical reference

- Eric W. Weisstein, **Pappus's Centroid Theorem**, MathWorld:
  <https://mathworld.wolfram.com/PappussCentroidTheorem.html>
- Consulted on 2026-11-15.
- The page states both standard formulas: surface area equals generating-curve
  length times the path length of its centroid, and volume equals generating
  area times the path length of its centroid.  It also records the customary
  non-repeated-covering/external-axis setting.

The proof in this archive is independently developed.  It replaces the usual
integral proof by finite polygonal and grid-cell identities plus explicit
primitive-recursive limits.

## ProveIt repository snapshot

Repository: <https://github.com/VladimirReshetnikov/ProveIt>

Pinned commit:

```text
8c135f6f2a9d041cde785a1a632c44ad98065b20
```

Commit timestamp observed through GitHub: 2026-11-15T20:31:36Z.

Relevant paths:

```text
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PRAToScalar.lean
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Interpretation.lean
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/BiInterpretation.lean
lakefile.toml
```

Interfaces used in the formalization plan:

- `PR`, `PTm`, `PRAAx`;
- `PRA.precZero`, `PRA.precSucc`, `PRA.qfInd`;
- `FromPRA.sigma`, `FromPRA.interp`;
- `Interp.sound`;
- `pra_iff_teq`, `pra_theorem_iff`.

The repository Lake configuration pins Mathlib `v4.32.0` at the observed
snapshot.

## Local build environment

- TeX Live pdfTeX 1.40.26 (2025 development distribution in the container).
- Python standard library exact arithmetic (`fractions.Fraction`).
- Lean/Lake was not installed locally; the Lean files were therefore not
  kernel-checked in this build environment.  This limitation is stated in the
  report and README.
