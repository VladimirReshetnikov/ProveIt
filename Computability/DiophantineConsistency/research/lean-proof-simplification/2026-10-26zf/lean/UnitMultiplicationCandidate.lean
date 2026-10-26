import DiophantineConsistency.ObjectDistributivity

/-!
Source-level candidate, not compiler-checked in this session.
The source theorem keeps exactly its current statement.  The left-successor
law at zero already gives multiplication by one, so no new internal induction
or external identification of internal omega with Nat is required.
-/

namespace ProofDelta.UnitMultiplication
open DiophantineConsistency
open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency ObjectArithmetic ObjectMultiplication
open ObjectAdditionLaws ObjectMultiplicationLaws

universe u
variable {V : Type u} {mem : V → V → Prop}

theorem mulRel_one_left (H : ZFAxioms mem) {y : V}
    (hy : mem y (omegaV H)) : MulRel H (natV H 1) y y :=
  mulRel_succ_left H (mulRel_zero_left H hy) (addRel_zero_left H hy)

-- Independent expression of the same idea, useful if inspecting the exact
-- specialization of the right-successor constructor is preferable.
theorem mulRel_one_left_via_comm (H : ZFAxioms mem) {y : V}
    (hy : mem y (omegaV H)) : MulRel H (natV H 1) y y := by
  have h := mulRel_succ H (mulRel_zero H hy)
  rw [addValue_zero_left H hy] at h
  exact mulRel_comm H h

#print axioms mulRel_one_left
#print axioms mulRel_one_left_via_comm

end ProofDelta.UnitMultiplication
