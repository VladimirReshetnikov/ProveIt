import ConciseIPRA.NativeBiInterpretation

/-!
# Object-language boundary

STATUS: proposed source, not compiler-checked in the authoring environment.
This file intentionally does not announce a formalized Euler theorem.

The source interfaces below were read at ProveIt commit
c1bda76f7f86d2ade505355980826f625e36fff3.
-/

namespace ConstructiveRotation

open LeanProofs.ConciseIPRA

/-- Three actual PR definitions, not a code passed to a purported total
universal primitive-recursive evaluator. Argument zero is the precision;
the remaining arguments are the natural parameters of a particular schema.

The intended rational is `(positiveNumerator - negativeNumerator) /
(denominatorPredecessor + 1)`. Regularity and arithmetic properties require
separate object-language formulas and derivations.
-/
structure RationalNameSymbols (parameters : Nat) where
  positiveNumerator : PR (parameters + 1)
  negativeNumerator : PR (parameters + 1)
  denominatorPredecessor : PR (parameters + 1)

abbrev MatrixNameSymbols (parameters : Nat) :=
  Fin 3 → Fin 3 → RationalNameSymbols parameters

/-- Existing repository transport applied to an already completed iPRA
derivation. This is only a transport lemma, not the missing derivation. -/
theorem transport_completed_derivation {n : Nat} {φ : Fm PTm n}
    (h : Prf PRAAx [] φ) : NPrf [] (NFm.ofPRA φ) := by
  have h' := (pra_iff_native (Γ := []) (φ := φ)).mp h
  simpa using h'

end ConstructiveRotation
