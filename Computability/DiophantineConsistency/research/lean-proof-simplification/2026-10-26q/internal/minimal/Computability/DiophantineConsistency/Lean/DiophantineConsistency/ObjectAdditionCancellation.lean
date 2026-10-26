import DiophantineConsistency.ObjectAdditionLaws
import BoundedZFCConsistency.InternalSat

/-! # Cancellation for addition over internal omega -/

namespace DiophantineConsistency.ObjectAdditionCancellation
open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency ObjectArithmetic ObjectMultiplication ObjectAdditionLaws

set_option maxRecDepth 12000
universe u
variable {V : Type u} {mem : V → V → Prop}

private def cancellationStage : Form :=
  fAll (fAll (fAll (fImp (fAnd (addForm 0 2 3) (addForm 0 1 3)) (fEq 2 1))))

private theorem cancellationStage_spec (H : ZFAxioms mem) (n : V) (ee : Nat → V) :
    Sat mem (scons n ee) cancellationStage ↔
      ∀ x x' z, AddRel H x n z → AddRel H x' n z → x=x' := by
  constructor
  · intro h x x' z hx hx'
    exact h x x' z ⟨(addForm_spec H _ 0 2 3).mpr hx,(addForm_spec H _ 0 1 3).mpr hx'⟩
  · intro h x x' z hh
    exact h x x' z ((addForm_spec H _ 0 2 3).mp hh.1) ((addForm_spec H _ 0 1 3).mp hh.2)

theorem addRel_cancel_right (H : ZFAxioms mem) {x x' y z : V}
    (hx : AddRel H x y z) (hx' : AddRel H x' y z) : x=x' := by
  let ee : Nat → V := fun _ => vempty H
  have h : ∀ n, mem n (omegaV H) → Sat mem (scons n ee) cancellationStage := by
    apply omega_ind H cancellationStage ee
    · apply (cancellationStage_spec H _ ee).mpr
      intro a b c ha hb
      exact (addRel_unique H ha (addRel_zero H ha.1)).symm.trans
        (addRel_unique H hb (addRel_zero H hb.1))
    · intro n hn ih
      apply (cancellationStage_spec H _ ee).mpr
      intro a b c ha hb
      obtain ⟨u,hu⟩ := addRel_total H ha.1 hn
      obtain ⟨w,hw⟩ := addRel_total H hb.1 hn
      have eu : c=vsucc H u := addRel_unique H ha (addRel_succ H hu)
      have ew : c=vsucc H w := addRel_unique H hb (addRel_succ H hw)
      have e : u=w := vsucc_inj_omega H w (addRel_result_nat H hw) u (eu.symm.trans ew)
      exact (cancellationStage_spec H n ee).mp ih a b u hu (e.symm ▸ hw)
  exact (cancellationStage_spec H y ee).mp (h y hx.2.1) x x' z hx hx'

theorem addRel_cancel_left (H : ZFAxioms mem) {x y y' z : V}
    (hy : AddRel H x y z) (hy' : AddRel H x y' z) : y=y' :=
  addRel_cancel_right H (addRel_comm H hy) (addRel_comm H hy')

theorem addValue_cancel_right (H : ZFAxioms mem) {x x' y : V}
    (hx : mem x (omegaV H)) (hx' : mem x' (omegaV H)) (hy : mem y (omegaV H))
    (he : addValue H x y=addValue H x' y) : x=x' := by
  exact addRel_cancel_right H (addValue_rel H hx hy) (he.symm ▸ addValue_rel H hx' hy)

theorem addValue_cancel_left (H : ZFAxioms mem) {x y y' : V}
    (hx : mem x (omegaV H)) (hy : mem y (omegaV H)) (hy' : mem y' (omegaV H))
    (he : addValue H x y=addValue H x y') : y=y' := by
  exact addRel_cancel_left H (addValue_rel H hx hy) (he.symm ▸ addValue_rel H hx hy')

/-- There is no cancellation between two internal nonnegative summands. -/
theorem addRel_zero_iff (H : ZFAxioms mem) (x y : V) :
    AddRel H x y (vempty H) ↔ x=vempty H ∧ y=vempty H := by
  constructor
  · intro hxy
    rcases nat_zero_or_succ H y hxy.2.1 with rfl | ⟨n,hn,rfl⟩
    · exact ⟨(addRel_unique H hxy (addRel_zero H hxy.1)).symm,rfl⟩
    · obtain ⟨b,hb⟩ := addRel_total H hxy.1 hn
      have he : vempty H=vsucc H b := addRel_unique H hxy (addRel_succ H hb)
      have hmem := vsucc_self H b
      rw [← he] at hmem
      exact False.elim (vempty_spec H b hmem)
  · rintro ⟨rfl,rfl⟩
    exact addRel_zero H (vempty_in_omega H)

theorem addValue_eq_zero_iff (H : ZFAxioms mem) {x y : V}
    (hx : mem x (omegaV H)) (hy : mem y (omegaV H)) :
    addValue H x y=vempty H ↔ x=vempty H ∧ y=vempty H := by
  constructor
  · intro he
    exact (addRel_zero_iff H x y).mp (he ▸ addValue_rel H hx hy)
  · intro h
    exact addRel_unique H (addValue_rel H hx hy) ((addRel_zero_iff H x y).mpr h)

def additionCancellationForm : Form := sealF (fAll cancellationStage)

theorem sentence_additionCancellationForm : Sentence additionCancellationForm := Sentence_seal _

theorem zfc_proves_addition_cancellation : BProv ZFCax_s [] additionCancellationForm := by
  apply completeness_inf_context ZFCax_s [] _ Sentences_ZFC
  intro Dom m v hmodel _
  let H := ObjectMultiplication.axioms_of_zfc_model v hmodel
  apply (seal_valid (mem := m) _).mpr ?_ v
  intro ee n
  apply (cancellationStage_spec H n ee).mpr
  intro x x' z hx hx'
  exact addRel_cancel_right H hx hx'

end DiophantineConsistency.ObjectAdditionCancellation
