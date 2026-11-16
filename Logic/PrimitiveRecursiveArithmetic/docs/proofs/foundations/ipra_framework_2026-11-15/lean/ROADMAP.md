# Lean implementation stages and exact certification status

No Lean executable was available in the authoring runtime. Neither Lean file has been typechecked. The native `FiniteCore.lean` contains definitions and elementary recursion-equation lemmas; it does not assert the main universal invariants. `ObjectTheoryBlueprint.lean` imports the actual repository module and deliberately contains no `axiom`/`sorry`, but also does not pretend to construct any object-level proof.

1. Pin Lean v4.32.0 and the repository `ConciseIPRA` project (the Basel packet reports this toolchain; re-check against the current lakefile).
2. Prove `testUpTo p n = true ↔ ∃ i < n, p i = true` by native induction; prove `firstUpTo` returns the least valid index (or sentinel).
3. Implement Boolean OR, comparisons, pairing, bound-indexed folds and iteration as actual `PR` syntax, with `PR.prec` using recursion argument first.
4. Internalize the loop invariants as QF formulas (`Fm PTm`) and derive them with `PRA.qfInd`. Use the defining equations `PRA.precZero`, `PRA.precSucc`, `PRA.comp` instead of assuming evaluation semantics.
5. Prove native-vs-PR evaluator correspondence as a **separate** theorem.
6. Implement signed fractions `(positive,negative,denominator)` with nonzero denominator and encode all real-name inequalities as PR natural comparison Booleans.
7. Build a compiler from certificate DAGs to composite `Prf` derivations, verifying composition and substitution once.
8. Revisit individual packets: Basel `checkBasel`, Puiseux exact algebraic code interface, Euler–Rodrigues gap certificates, finite Runge bounds; do not claim missing global height bounds.

The task is complete only after an explicit term of type `Γ ⊢[PRAAx] φ` has been constructed for each theorem. Existing external `Nat` proof scripts are not a substitute.
