import DiophantineConsistency.ObjectAdditionCancellation

/-! # Multiplication laws for all internal natural numbers -/

namespace DiophantineConsistency.ObjectMultiplicationLaws
open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency ObjectArithmetic ObjectMultiplication ObjectAdditionLaws

set_option maxRecDepth 16000
universe u
variable {V : Type u} {mem : V → V → Prop}

theorem addValue_zero_right (H : ZFAxioms mem) {x : V} (hx : mem x (omegaV H)) :
    addValue H x (vempty H)=x :=
  addRel_unique H (addValue_rel H hx (vempty_in_omega H)) (addRel_zero H hx)

theorem addValue_zero_left (H : ZFAxioms mem) {x : V} (hx : mem x (omegaV H)) :
    addValue H (vempty H) x=x :=
  addRel_unique H (addValue_rel H (vempty_in_omega H) hx) (addRel_zero_left H hx)

theorem addValue_succ_right (H : ZFAxioms mem) {x y : V}
    (hx : mem x (omegaV H)) (hy : mem y (omegaV H)) :
    addValue H x (vsucc H y)=vsucc H (addValue H x y) :=
  addRel_unique H (addValue_rel H hx (omega_succ H y hy)) (addRel_succ H (addValue_rel H hx hy))

theorem addValue_succ_left (H : ZFAxioms mem) {x y : V}
    (hx : mem x (omegaV H)) (hy : mem y (omegaV H)) :
    addValue H (vsucc H x) y=vsucc H (addValue H x y) :=
  addRel_unique H (addValue_rel H (omega_succ H x hx) hy)
    (addRel_succ_left H hy (addValue_rel H hx hy))

theorem mulRel_zero_left (H : ZFAxioms mem) {y : V} (hy : mem y (omegaV H)) :
    MulRel H (vempty H) y (vempty H) := by
  let ee : Nat → V := fun _ => vempty H
  have h : ∀ n, mem n (omegaV H) →
      Sat mem (scons n (scons (vempty H) ee)) (mulForm 1 1 0) := by
    apply omega_ind H (mulForm 1 1 0) (scons (vempty H) ee)
    · exact (mulForm_spec H _ 1 1 0).mpr (mulRel_zero H (vempty_in_omega H))
    · intro n _ ih
      exact (mulForm_spec H _ 1 1 0).mpr
        (mulRel_succ_of_add H ((mulForm_spec H _ 1 1 0).mp ih)
          (addRel_zero H (vempty_in_omega H)))
  exact (mulForm_spec H _ 1 1 0).mp (h y hy)

private def successorLeftStage : Form :=
  fAll (fAll (fImp (fAnd (mulForm 1 3 2) (addForm 0 1 2)) (mulForm 0 4 2)))

private theorem successorLeftStage_spec (H : ZFAxioms mem) (n x x' : V) (ee : Nat → V) :
    Sat mem (scons n (scons x (scons x' ee))) successorLeftStage ↔
      ∀ u v, MulRel H x n u → AddRel H u n v → MulRel H x' n v := by
  constructor
  · intro h u v hm ha
    exact (mulForm_spec H _ 0 4 2).mp
      (h u v ⟨(mulForm_spec H _ 1 3 2).mpr hm,(addForm_spec H _ 0 1 2).mpr ha⟩)
  · intro h u v hh
    exact (mulForm_spec H _ 0 4 2).mpr
      (h u v ((mulForm_spec H _ 1 3 2).mp hh.1) ((addForm_spec H _ 0 1 2).mp hh.2))

/-- The left-successor law, with its addition witness explicit. -/
theorem mulRel_succ_left (H : ZFAxioms mem) {x y z w : V}
    (hxy : MulRel H x y z) (hadd : AddRel H z y w) :
    MulRel H (vsucc H x) y w := by
  let ee : Nat → V := fun _ => vempty H
  have h : ∀ n, mem n (omegaV H) →
      Sat mem (scons n (scons x (scons (vsucc H x) ee))) successorLeftStage := by
    apply omega_ind H successorLeftStage (scons x (scons (vsucc H x) ee))
    · apply (successorLeftStage_spec H _ x (vsucc H x) ee).mpr
      intro u v hm ha
      have eu : u=vempty H := mulRel_unique H hm (mulRel_zero H hxy.1)
      have ev : v=u := addRel_unique H ha (addRel_zero H (mulRel_result_nat H hm))
      rw [ev,eu]
      exact mulRel_zero H (omega_succ H x hxy.1)
    · intro n hn ih
      apply (successorLeftStage_spec H _ x (vsucc H x) ee).mpr
      intro u v hm ha
      obtain ⟨u0,hu0⟩ := mulRel_total H hxy.1 hn
      have huNat := mulRel_result_nat H hu0
      let v0 := addValue H u0 n
      have hv0 : AddRel H u0 n v0 := addValue_rel H huNat hn
      have hvNat := addRel_result_nat H hv0
      have hp := (successorLeftStage_spec H n x (vsucc H x) ee).mp ih u0 v0 hu0 hv0
      have eu : u=addValue H u0 x := mulRel_unique H hm (mulRel_succ H hu0)
      have ev : v=addValue H u (vsucc H n) := addRel_unique H ha
        (addValue_rel H (mulRel_result_nat H hm) (omega_succ H n hn))
      have algebra : addValue H (addValue H u0 x) (vsucc H n)=
          addValue H v0 (vsucc H x) := by
        calc
          addValue H (addValue H u0 x) (vsucc H n) =
              vsucc H (addValue H (addValue H u0 x) n) :=
            addValue_succ_right H (addRel_result_nat H (addValue_rel H huNat hxy.1)) hn
          _ = vsucc H (addValue H u0 (addValue H x n)) :=
            congrArg (vsucc H) (addValue_assoc H huNat hxy.1 hn)
          _ = vsucc H (addValue H u0 (addValue H n x)) := by rw [addValue_comm H hxy.1 hn]
          _ = vsucc H (addValue H v0 x) :=
            congrArg (vsucc H) (addValue_assoc H huNat hn hxy.1).symm
          _ = addValue H v0 (vsucc H x) := (addValue_succ_right H hvNat hxy.1).symm
      have ev' : v=addValue H v0 (vsucc H x) := ev.trans (by rw [eu];exact algebra)
      rw [ev']
      exact mulRel_succ H hp
  exact (successorLeftStage_spec H y x (vsucc H x) ee).mp (h y hxy.2.1) z w hxy hadd

private def commutativeStage : Form :=
  fAll (fImp (mulForm 0 2 1) (mulForm 0 1 2))

private theorem commutativeStage_spec (H : ZFAxioms mem) (n x : V) (ee : Nat → V) :
    Sat mem (scons n (scons x ee)) commutativeStage ↔
      ∀ z, MulRel H x n z → MulRel H n x z := by
  constructor
  · intro h z hz
    exact (mulForm_spec H _ 0 1 2).mp (h z ((mulForm_spec H _ 0 2 1).mpr hz))
  · intro h z hz
    exact (mulForm_spec H _ 0 1 2).mpr (h z ((mulForm_spec H _ 0 2 1).mp hz))

theorem mulRel_comm (H : ZFAxioms mem) {x y z : V} (hxy : MulRel H x y z) :
    MulRel H y x z := by
  let ee : Nat → V := fun _ => vempty H
  have h : ∀ n, mem n (omegaV H) →
      Sat mem (scons n (scons x ee)) commutativeStage := by
    apply omega_ind H commutativeStage (scons x ee)
    · apply (commutativeStage_spec H _ x ee).mpr
      intro a ha
      have ea : a=vempty H := mulRel_unique H ha (mulRel_zero H hxy.1)
      rw [ea]
      exact mulRel_zero_left H hxy.1
    · intro n hn ih
      apply (commutativeStage_spec H _ x ee).mpr
      intro a ha
      obtain ⟨b,hb⟩ := mulRel_total H hxy.1 hn
      have hp := (commutativeStage_spec H n x ee).mp ih b hb
      have ea : a=addValue H b x := mulRel_unique H ha (mulRel_succ H hb)
      rw [ea]
      exact mulRel_succ_left H hp (addValue_rel H (mulRel_result_nat H hb) hxy.1)
  exact (commutativeStage_spec H y x ee).mp (h y hxy.2.1) z hxy

theorem mulRel_comm_iff (H : ZFAxioms mem) (x y z : V) :
    MulRel H x y z ↔ MulRel H y x z := ⟨mulRel_comm H,mulRel_comm H⟩

def multiplicationCommutativeForm : Form := sealF
  (fAll (fAll (fAll (fImp (mulForm 0 2 1) (mulForm 0 1 2)))))

theorem sentence_multiplicationCommutativeForm : Sentence multiplicationCommutativeForm :=
  Sentence_seal _

theorem zfc_proves_multiplication_commutative : BProv ZFCax_s [] multiplicationCommutativeForm := by
  apply completeness_inf_context ZFCax_s [] _ Sentences_ZFC
  intro Dom m v hmodel _
  let H := ObjectMultiplication.axioms_of_zfc_model v hmodel
  apply (seal_valid (mem := m) _).mpr ?_ v
  intro ee x y z h
  exact (mulForm_spec H _ 0 1 2).mpr (mulRel_comm H ((mulForm_spec H _ 0 2 1).mp h))

end DiophantineConsistency.ObjectMultiplicationLaws
