# Sources and provenance

Prepared 15 November 2026.

## Requested theorem

- Eric W. Weisstein, Puiseux's Theorem, MathWorld:
  https://mathworld.wolfram.com/PuiseuxsTheorem.html
- The retrieved statement explicitly includes convergence, finite-limit
  parametrizations, and Laurent expansions for branches tending to infinity.

## Primary mathematical context

- Bassel Mannaa and Thierry Coquand, Dynamic Newton–Puiseux theorem,
  Journal of Logic and Analysis 5:5 (2013), 1–22:
  https://doi.org/10.4115/jla.2013.5.5
  https://math.hawaii.edu/home/jla/152-672-1-PB.pdf
- Curtis T. McMullen, Riemann Surfaces, Harvard Math 213b notes,
  28 April 2026, pp. 44–45:
  https://abel.math.harvard.edu/~ctm/math213b/home/course/course.pdf

The main report gives its own explicit finite coefficient bounds,
desingularization, majorant proof, and exact-code construction. The
analytic/topological proof in the course notes is not imported as an
iPRA proof.

## ProveIt snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Commit: d851229c33ef395db8dc04baf28c6a291073f61e

Commit timestamp: 2026-11-15T19:58:15Z

Declared toolchain: leanprover/lean4:v4.32.0

Inspected paths:

- Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md
- Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Syntax.lean
- Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean
- Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean
- Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Interpretation.lean
- Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean
- docs/drafts/ (directory inventory)
- docs/drafts/FTA_iPRA.zip

Pinned directory:
https://github.com/VladimirReshetnikov/ProveIt/tree/d851229c33ef395db8dc04baf28c6a291073f61e/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

## Frozen FTA dependency

Source:
https://github.com/VladimirReshetnikov/ProveIt/blob/d851229c33ef395db8dc04baf28c6a291073f61e/docs/drafts/FTA_iPRA.zip

Git blob SHA: 60f15e1faa33b18ebbcb0a61f7fcccaa8b36aaf5

Original archive size: 413411 bytes

Original archive SHA-256:
8de676594df9fe7809adff19fe2a611aac94fe2c7f17ac3db92d2ecb7cf00564

The archive's contents are extracted unchanged into dependencies/FTA_iPRA/.
Their original provenance and integrity files are retained.
Reuse is limited to its human-readable single-root theorem with a fixed
primitive recursive coefficient evaluator. Its Lean specification is
uncompiled, and its fixed-degree numerical factorization discussion is not
assumed to provide a degree-uniform numerical deflation theorem.

## New artifacts and verification boundary

- The new mathematical result is stated for exact algebraic presentations.
- The Python examples use exact Gaussian-rational arithmetic.
- The mathematical audits in evidence/ are review notes, not proof certificates.
- No Lean compilation was possible in this environment.
- The supplied Lean interface contains no completed Puiseux derivation.
- The main PDF is compiled from the supplied main TeX and three section files.
