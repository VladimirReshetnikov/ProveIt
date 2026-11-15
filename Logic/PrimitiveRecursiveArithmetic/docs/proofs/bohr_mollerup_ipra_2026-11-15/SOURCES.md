# Sources and repository anchors

## Standard theorem references

- NIST Digital Library of Mathematical Functions, Chapter 5, Section 5.5(iv),
  Bohr–Mollerup theorem.
- The Wikipedia article “Bohr–Mollerup theorem,” used only to cross-check the
  familiar Euler-bracket squeeze and indexing.
- Mathlib file
  `Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean`, especially
  `Real.eq_Gamma_of_log_convex`, used as a theorem-name and regression
  reference. The constructive proof in this archive does not invoke that
  theorem.

## ProveIt repository anchors

Repository: `VladimirReshetnikov/ProveIt`

Repository state inspected while preparing this package:

```text
0bba41d70f061442357cae0f6de055434a33fb09
```

Relevant paths:

```text
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/BiInterpretation.lean
docs/drafts/
```

`PR.lean` provides the usual first-order iPRA presentation (`PR`, `PTm`,
`PRAAx`, and `PRA.qfInd`). `BiInterpretation.lean` provides the faithful
translation and `pra_theorem_iff` bridge to the concise scalar theory.

## Constructive-analysis background

- Errett Bishop and Douglas Bridges, *Constructive Analysis*, Springer, 1985.
