import DiophantineConsistency.ObjectMultiplication

/-! # Addition laws over every ZF model's internal omega

Each induction below supplies an actual set-theory formula. Thus the laws
apply to nonstandard internal naturals, not only quoted external numerals.
-/

namespace DiophantineConsistency.ObjectAdditionLaws
open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency ObjectArithmetic ObjectMultiplication

set_option maxRecDepth 12000

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- Iterating successor from zero returns every internal natural itself. -/
theorem addRel_zero_left (H : ZFAxioms mem) {y : V} (hy : mem y (omegaV H)) :
    AddRel H (vempty H) y y := by
  let ee : Nat → V := fun _ => vempty H
  have h : ∀ n, mem n (omegaV H) →
      Sat mem (scons n (scons (vempty H) ee)) (addForm 0 1 0) := by
    apply omega_ind H (addForm 0 1 0) (scons (vempty H) ee)
    · exact (addForm_spec H _ 0 1 0).mpr (addRel_zero H (vempty_in_omega H))
    · intro n _ ih
      exact (addForm_spec H _ 0 1 0).mpr
        (addRel_succ H ((addForm_spec H _ 0 1 0).mp ih))
  exact (addForm_spec H _ 0 1 0).mp (h y hy)

private def successorLeftStage : Form :=
  fAll (fImp (addForm 0 2 1)
    (fEx (fAnd (fSuccF 0 1)
      (fEx (fAnd (fSuccF 0 4) (addForm 1 0 3))))))

private theorem successorLeftStage_spec (H : ZFAxioms mem) (n x : V) (ee : Nat → V) :
    Sat mem (scons n (scons x ee)) successorLeftStage ↔
      ∀ z, AddRel H x n z → AddRel H (vsucc H x) n (vsucc H z) := by
  simp only [successorLeftStage, Sat, addForm_spec H, fSuccF_spec H, scons, exists_eq_left]

/-- Successor can be moved through the left input, for all internal naturals. -/
theorem addRel_succ_left (H : ZFAxioms mem) {x y z : V}
    (hy : mem y (omegaV H)) (hxy : AddRel H x y z) :
    AddRel H (vsucc H x) y (vsucc H z) := by
  let ee : Nat → V := fun _ => vempty H
  have h : ∀ n, mem n (omegaV H) →
      Sat mem (scons n (scons x ee)) successorLeftStage := by
    apply omega_ind H successorLeftStage (scons x ee)
    · apply (successorLeftStage_spec H _ x ee).mpr
      intro a ha
      have he : a=x := addRel_unique H ha (addRel_zero H hxy.1)
      rw [he]
      exact addRel_zero H (omega_succ H x hxy.1)
    · intro n hn ih
      apply (successorLeftStage_spec H _ x ee).mpr
      intro a ha
      obtain ⟨b,hb⟩ := addRel_total H hxy.1 hn
      have hleft := (successorLeftStage_spec H n x ee).mp ih b hb
      have he : a=vsucc H b := addRel_unique H ha (addRel_succ H hb)
      rw [he]
      exact addRel_succ H hleft
  exact (successorLeftStage_spec H y x ee).mp (h y hy) z hxy

private def commutativeStage : Form :=
  fAll (fImp (addForm 0 2 1) (addForm 0 1 2))

private theorem commutativeStage_spec (H : ZFAxioms mem) (n x : V) (ee : Nat → V) :
    Sat mem (scons n (scons x ee)) commutativeStage ↔
      ∀ z, AddRel H x n z → AddRel H n x z := by
  simp only [commutativeStage, Sat, addForm_spec H, scons]

theorem addRel_comm (H : ZFAxioms mem) {x y z : V} (hxy : AddRel H x y z) :
    AddRel H y x z := by
  let ee : Nat → V := fun _ => vempty H
  have h : ∀ n, mem n (omegaV H) →
      Sat mem (scons n (scons x ee)) commutativeStage := by
    apply omega_ind H commutativeStage (scons x ee)
    · apply (commutativeStage_spec H _ x ee).mpr
      intro a ha
      have he : a=x := addRel_unique H ha (addRel_zero H hxy.1)
      rw [he]
      exact addRel_zero_left H hxy.1
    · intro n hn ih
      apply (commutativeStage_spec H _ x ee).mpr
      intro a ha
      obtain ⟨b,hb⟩ := addRel_total H hxy.1 hn
      have hcomm := (commutativeStage_spec H n x ee).mp ih b hb
      have he : a=vsucc H b := addRel_unique H ha (addRel_succ H hb)
      rw [he]
      exact addRel_succ_left H hxy.1 hcomm
  exact (commutativeStage_spec H y x ee).mp (h y hxy.2.1) z hxy

theorem addRel_comm_iff (H : ZFAxioms mem) (x y z : V) :
    AddRel H x y z ↔ AddRel H y x z :=
  ⟨addRel_comm H,addRel_comm H⟩

private def associativeStage : Form :=
  fAll (fAll (fImp (fAnd (addForm 1 4 2) (addForm 0 5 2)) (addForm 0 3 1)))

private theorem associativeStage_spec (H : ZFAxioms mem) (n x y a : V) (ee : Nat → V) :
    Sat mem (scons n (scons x (scons y (scons a ee)))) associativeStage ↔
      ∀ b z, AddRel H y n b → AddRel H a n z → AddRel H x b z := by
  simp only [associativeStage, Sat, addForm_spec H, scons, and_imp]

/-- Associativity with every intermediate value explicit. -/
theorem addRel_assoc (H : ZFAxioms mem) {x y n a b z : V}
    (hxy : AddRel H x y a) (hyn : AddRel H y n b) (han : AddRel H a n z) :
    AddRel H x b z := by
  let ee : Nat → V := fun _ => vempty H
  have haNat := addRel_result_nat H hxy
  have h : ∀ k, mem k (omegaV H) →
      Sat mem (scons k (scons x (scons y (scons a ee)))) associativeStage := by
    apply omega_ind H associativeStage (scons x (scons y (scons a ee)))
    · apply (associativeStage_spec H _ x y a ee).mpr
      intro b' z' hb hz
      have eb : b'=y := addRel_unique H hb (addRel_zero H hxy.2.1)
      have ez : z'=a := addRel_unique H hz (addRel_zero H haNat)
      rw [eb,ez]
      exact hxy
    · intro k hk ih
      apply (associativeStage_spec H _ x y a ee).mpr
      intro b' z' hb hz
      obtain ⟨b0,hb0⟩ := addRel_total H hxy.2.1 hk
      obtain ⟨z0,hz0⟩ := addRel_total H haNat hk
      have hp := (associativeStage_spec H k x y a ee).mp ih b0 z0 hb0 hz0
      have eb : b'=vsucc H b0 := addRel_unique H hb (addRel_succ H hb0)
      have ez : z'=vsucc H z0 := addRel_unique H hz (addRel_succ H hz0)
      rw [eb,ez]
      exact addRel_succ H hp
  exact (associativeStage_spec H n x y a ee).mp (h n hyn.2.1) b z hyn han

theorem addRel_assoc_iff (H : ZFAxioms mem) {x y n a b z : V}
    (hxy : AddRel H x y a) (hyn : AddRel H y n b) :
    AddRel H a n z ↔ AddRel H x b z := by
  constructor
  · exact addRel_assoc H hxy hyn
  · intro hxb
    exact addRel_comm H
      (addRel_assoc H (addRel_comm H hyn) (addRel_comm H hxy) (addRel_comm H hxb))

theorem addValue_comm (H : ZFAxioms mem) {x y : V}
    (hx : mem x (omegaV H)) (hy : mem y (omegaV H)) :
    addValue H x y=addValue H y x :=
  addRel_unique H (addRel_comm H (addValue_rel H hx hy)) (addValue_rel H hy hx)

theorem addValue_assoc (H : ZFAxioms mem) {x y n : V}
    (hx : mem x (omegaV H)) (hy : mem y (omegaV H)) (hn : mem n (omegaV H)) :
    addValue H (addValue H x y) n=addValue H x (addValue H y n) := by
  have hxy := addValue_rel H hx hy
  have hyn := addValue_rel H hy hn
  have han := addValue_rel H (addRel_result_nat H hxy) hn
  exact addRel_unique H (addRel_assoc H hxy hyn han)
    (addValue_rel H hx (addRel_result_nat H hyn))

/-- A closed commutativity sentence for the actual internal addition graph. -/
def additionCommutativeForm : Form := sealF
  (fAll (fAll (fAll (fImp (addForm 0 2 1) (addForm 0 1 2)))))

theorem sentence_additionCommutativeForm : Sentence additionCommutativeForm :=
  Sentence_seal _

/-- An actual derivation inside sealed ZFC, without a consistency assumption. -/
theorem zfc_proves_addition_commutative : BProv ZFCax_s [] additionCommutativeForm := by
  apply completeness_inf_context ZFCax_s [] _ Sentences_ZFC
  intro Dom m v hmodel _
  let H := ObjectMultiplication.axioms_of_zfc_model v hmodel
  apply (seal_valid (mem := m) _).mpr ?_ v
  intro ee x y z h
  exact (addForm_spec H _ 0 1 2).mpr (addRel_comm H ((addForm_spec H _ 0 2 1).mp h))

def additionAssociativeForm : Form := sealF
  (fAll (fAll (fAll (fAll (fAll (fAll
    (fImp (fAnd (addForm 2 5 4) (fAnd (addForm 1 4 3) (addForm 0 2 3)))
      (addForm 0 5 1))))))))

theorem sentence_additionAssociativeForm : Sentence additionAssociativeForm := Sentence_seal _

theorem zfc_proves_addition_associative : BProv ZFCax_s [] additionAssociativeForm := by
  apply completeness_inf_context ZFCax_s [] _ Sentences_ZFC
  intro Dom m v hmodel _
  let H := ObjectMultiplication.axioms_of_zfc_model v hmodel
  apply (seal_valid (mem := m) _).mpr ?_ v
  intro ee x y n a b z h
  exact (addForm_spec H _ 0 5 1).mpr
    (addRel_assoc H ((addForm_spec H _ 2 5 4).mp h.1)
      ((addForm_spec H _ 1 4 3).mp h.2.1) ((addForm_spec H _ 0 2 3).mp h.2.2))

end DiophantineConsistency.ObjectAdditionLaws
