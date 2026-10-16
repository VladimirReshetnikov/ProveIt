import BusyBeaver.ZFC.TarskiComplete
import BusyBeaver.ZFC.TarskiClassicalBridge

/-!
# Unconditional completeness of the exact Tarski logical rows

This wrapper discharges both propositional hypotheses of the repository's
`Tarski.completeness` theorem using the explicit Lukasiewicz reconstruction
and the existing `rho6` falsity bridge. It adds no machine rows.

The conclusion concerns the named-variable formula calculus with primitive
Bottom. Numerical code aliases, axiom enumeration, register execution,
binary Turing-machine simulation and internal consistency calibration are
separate statements; this file does not assert any of them.
-/

namespace SetTheory.BusyBeaver.ZFC.Tarski

variable {Ax : NF → Prop}

/-- Completeness with no unproved propositional hypotheses. -/
theorem completeness_closed (f : NF)
    (hval : ∀ (D : Type) (mem : D → D → Prop),
      (∀ a, Ax a → ∀ e : Nat → D, Sat mem e a) →
      ∀ e : Nat → D, Sat mem e f) : Thm Ax f :=
  completeness classical_from_rows classical_from_rows f hval

/-- The exact calculus defines ordinary first-order consequence. -/
theorem theorem_iff_semantic_consequence (f : NF) :
    Thm Ax f ↔ ∀ (D : Type) (mem : D → D → Prop),
      (∀ a, Ax a → ∀ e : Nat → D, Sat mem e a) →
      ∀ e : Nat → D, Sat mem e f := by
  constructor
  · intro hf D mem hAx e
    exact soundness hAx hf e
  · exact completeness_closed f

#print axioms completeness_closed
#print axioms theorem_iff_semantic_consequence

end SetTheory.BusyBeaver.ZFC.Tarski
