# Source provenance and verification boundary

Prepared November 14, 2026 (America/Los_Angeles).

## Mathematical sources

The requested theorem:

- https://en.wikipedia.org/wiki/Fundamental_theorem_of_algebra

Primary background on constructive Kneser descent and a Coq formalization:

- Herman Geuvers, Freek Wiedijk, Jan Zwanenburg, *A Constructive Proof of the
  Fundamental Theorem of Algebra without using the Rationals*.
  https://www.cs.ru.nl/~freek/pubs/kneser.pdf

The article develops its finite rational estimates and constructions
self-containedly. No FTA theorem from a stronger system is a proof premise.
The rational direction lemma uses finite square-root bisection and a finite
binomial-polynomial identity, not FTA or a trigonometric root oracle.

## ProveIt snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Commit: `b03925cccc76d55b9dc2a00864a5e0544b64aa7f`.

The commit timestamp is 2026-11-15T04:30:26Z (November 14 in Los Angeles).
The root toolchain and Lake configuration name Lean/mathlib v4.32.0.
This was a read-only source inspection, not an independent build.

Recommended foundation under
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/`:

- `PR.lean`: PR syntax, arithmetic terms, `PRAAx`, `PRA.qfInd`.
- `Deduction.lean`: deeply embedded intuitionistic derivability.
- `Syntax.lean`: syntax and substitution conventions.
- `BiInterpretation.lean`: `pra_iff_teq` and related translations.
- `NativeBiInterpretation.lean`: `pra_iff_native` and round-trip results.

Pinned primary source:
https://github.com/VladimirReshetnikov/ProveIt/blob/b03925cccc76d55b9dc2a00864a5e0544b64aa7f/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean

Other requested directories were inspected for possible reuse:

- `Computability/DiophantineConsistency`: an alternative iPRA presentation,
  finite PR syntax and related arithmetic infrastructure. Not a required
  dependency of the proposed proof.
- `Computability/BusyBeaver/Research/ZFC`: machine and consistency
  infrastructure. No theorem from it is used as an FTA premise.

## Verification performed for this package

- The handwritten constants and mathematical steps were independently
  reviewed during preparation.
- Seven direction examples passed exact rational certificate checks.
- Six local descent examples passed exact residual and radius checks.
- The LaTeX source was compiled and its rendered PDF was inspected.
- No Lean build was run. The Lean artifact is an uncompiled outline and
  specification, not a certified proof. No missing FTA theorem is postulated.

The test logs contain finite computational evidence. The theorem and its
logical-strength claim are justified by the written argument, pending the
outlined full object-level formalization.
