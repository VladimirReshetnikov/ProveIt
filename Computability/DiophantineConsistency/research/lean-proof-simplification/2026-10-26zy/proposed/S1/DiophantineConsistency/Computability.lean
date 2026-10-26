import DiophantineConsistency.DirectScalarEnumerator
import Mathlib.Computability.RE

/-! Computability supplied by the existing literal scalar program. -/

namespace DiophantineConsistency

open SetTheory SetTheory.BusyBeaver.ZFC
open EnumPerm Code254 KCode222

/-- Reuse the supplied program rather than reprove every arithmetic constructor. -/
theorem haltingTest_natPrimrec : Nat.Primrec haltingTest :=
  DirectEnumerator.program.val.primrec.of_eq DirectEnumerator.program.property

theorem haltingTest_vectorPrimrec :
    Nat.Primrec' (fun v : List.Vector ℕ 1 => haltingTest v.head) :=
  Nat.Primrec'.prim_iff₁.mpr (Primrec.nat_iff.mpr haltingTest_natPrimrec)

/-- The actual refutation predicate is recursively enumerable. -/
theorem refutationInputs_re : REPred refutationInputs := by
  have ht : Primrec fun v : ℕ × ℕ => decide (haltingTest v.2 = 1) :=
    (Primrec.eq.comp
      ((Primrec.nat_iff.mpr haltingTest_natPrimrec).comp Primrec.snd)
      (Primrec.const 1)).decide
  have hsearch : Partrec fun _ : ℕ => Nat.rfind
      (fun t => Part.some (decide (haltingTest t = 1))) :=
    Partrec.rfind ht.to_comp.partrec
  apply hsearch.dom_re.of_eq
  intro _
  simp only [Nat.rfind_dom, Part.mem_some_iff, true_eq_decide_iff,
    Part.some_dom, implies_true, and_true]
  exact exists_haltingTest_eq_one_iff

end DiophantineConsistency
