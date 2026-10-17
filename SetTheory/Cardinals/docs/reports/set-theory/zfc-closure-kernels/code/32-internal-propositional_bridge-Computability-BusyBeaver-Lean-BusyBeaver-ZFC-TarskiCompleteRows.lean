import BusyBeaver.ZFC.Lukasiewicz
import BusyBeaver.ZFC.TarskiComplete

/-!
The exact emitted Tarski rows have unconditional first-order completeness.
This is an integration theorem: it discharges the two explicit propositional
hypotheses of the pinned TarskiComplete.completeness result using the
attributed CD254 certificate port and the rho6 ex-falso argument.
It says nothing about numerical code aliases, machine execution, or Con(ZFC).
-/

namespace SetTheory.BusyBeaver.ZFC.Tarski

open NF
variable {Ax : NF → Prop}

theorem completeness_from_rows (f : NF)
    (hval : ∀ (D : Type) (mem : D → D → Prop),
      (∀ a, Ax a → ∀ e : Nat → D, Sat mem e a) → ∀ e : Nat → D, Sat mem e f) :
    Thm Ax f :=
  completeness (classical_from_rows Ax) (classical_from_rows (fun _ => False)) f hval

theorem theorem_iff_valid (f : NF) : Thm Ax f ↔
    (∀ (D : Type) (mem : D → D → Prop),
      (∀ a, Ax a → ∀ e : Nat → D, Sat mem e a) → ∀ e : Nat → D, Sat mem e f) := by
  constructor
  · intro h D mem hAx e
    exact soundness hAx h e
  · exact completeness_from_rows f

end SetTheory.BusyBeaver.ZFC.Tarski

#print axioms SetTheory.BusyBeaver.ZFC.Tarski.completeness_from_rows
#print axioms SetTheory.BusyBeaver.ZFC.Tarski.theorem_iff_valid
