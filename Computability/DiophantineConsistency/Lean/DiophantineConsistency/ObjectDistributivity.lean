import DiophantineConsistency.ObjectMultiplicationLaws

/-! # Distributivity and multiplication associativity over internal omega -/

namespace DiophantineConsistency.ObjectDistributivity
open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency ObjectArithmetic ObjectMultiplication
open ObjectAdditionLaws ObjectMultiplicationLaws

set_option maxRecDepth 20000
universe u
variable {V : Type u} {mem : V → V → Prop}

private def distributiveStage : Form :=
  fAll (fAll (fAll (fImp
    (fAnd (addForm 2 5 3) (fAnd (mulForm 1 4 3) (addForm 0 6 1)))
    (mulForm 0 4 2))))

private theorem distributiveStage_spec (H : ZFAxioms mem) (n x y b : V) (ee : Nat → V) :
    Sat mem (scons n (scons x (scons y (scons b ee)))) distributiveStage ↔
      ∀ a c d, AddRel H y n a → MulRel H x n c → AddRel H b c d → MulRel H x a d := by
  constructor
  · intro h a c d ha hc hd
    exact (mulForm_spec H _ 0 4 2).mp (h a c d
      ⟨(addForm_spec H _ 2 5 3).mpr ha,
        (mulForm_spec H _ 1 4 3).mpr hc,(addForm_spec H _ 0 6 1).mpr hd⟩)
  · intro h a c d hh
    exact (mulForm_spec H _ 0 4 2).mpr
      (h a c d ((addForm_spec H _ 2 5 3).mp hh.1)
        ((mulForm_spec H _ 1 4 3).mp hh.2.1) ((addForm_spec H _ 0 6 1).mp hh.2.2))

/-- Every intermediate sum and product is explicit; no external numeral bound. -/
theorem mulRel_distrib_left (H : ZFAxioms mem) {x y n a b c d : V}
    (ha : AddRel H y n a) (hb : MulRel H x y b)
    (hc : MulRel H x n c) (hd : AddRel H b c d) : MulRel H x a d := by
  let ee : Nat → V := fun _ => vempty H
  have hbNat := mulRel_result_nat H hb
  have h : ∀ k, mem k (omegaV H) →
      Sat mem (scons k (scons x (scons y (scons b ee)))) distributiveStage := by
    apply omega_ind H distributiveStage (scons x (scons y (scons b ee)))
    · apply (distributiveStage_spec H _ x y b ee).mpr
      intro a' c' d' ha' hc' hd'
      have ea : a'=y := addRel_unique H ha' (addRel_zero H hb.2.1)
      have ec : c'=vempty H := mulRel_unique H hc' (mulRel_zero H hb.1)
      have ed : d'=b := by
        rw [ec] at hd'
        exact addRel_unique H hd' (addRel_zero H hbNat)
      rw [ea,ed]
      exact hb
    · intro k hk ih
      apply (distributiveStage_spec H _ x y b ee).mpr
      intro a' c' d' ha' hc' hd'
      obtain ⟨a0,ha0⟩ := addRel_total H hb.2.1 hk
      obtain ⟨c0,hc0⟩ := mulRel_total H hb.1 hk
      have hcNat := mulRel_result_nat H hc0
      let d0 := addValue H b c0
      have hd0 : AddRel H b c0 d0 := addValue_rel H hbNat hcNat
      have hp := (distributiveStage_spec H k x y b ee).mp ih a0 c0 d0 ha0 hc0 hd0
      have ea : a'=vsucc H a0 := addRel_unique H ha' (addRel_succ H ha0)
      have ec : c'=addValue H c0 x := mulRel_unique H hc' (mulRel_succ H hc0)
      have ed : d'=addValue H b c' := addRel_unique H hd'
        (addValue_rel H hbNat (mulRel_result_nat H hc'))
      have ed' : d'=addValue H d0 x := by
        rw [ed,ec,← addValue_assoc H hbNat hcNat hb.1]
      rw [ea,ed']
      exact mulRel_succ H hp
  exact (distributiveStage_spec H n x y b ee).mp (h n ha.2.1) a c d ha hc hd

theorem mulRel_distrib_right (H : ZFAxioms mem) {x y n a b c d : V}
    (ha : AddRel H y n a) (hb : MulRel H y x b)
    (hc : MulRel H n x c) (hd : AddRel H b c d) : MulRel H a x d :=
  mulRel_comm H (mulRel_distrib_left H ha (mulRel_comm H hb) (mulRel_comm H hc) hd)

private def associativeStage : Form :=
  fAll (fAll (fImp (fAnd (mulForm 1 4 2) (mulForm 0 5 2)) (mulForm 0 3 1)))

private theorem associativeStage_spec (H : ZFAxioms mem) (n x y a : V) (ee : Nat → V) :
    Sat mem (scons n (scons x (scons y (scons a ee)))) associativeStage ↔
      ∀ b z, MulRel H y n b → MulRel H a n z → MulRel H x b z := by
  constructor
  · intro h b z hb hz
    exact (mulForm_spec H _ 0 3 1).mp
      (h b z ⟨(mulForm_spec H _ 1 4 2).mpr hb,(mulForm_spec H _ 0 5 2).mpr hz⟩)
  · intro h b z hh
    exact (mulForm_spec H _ 0 3 1).mpr
      (h b z ((mulForm_spec H _ 1 4 2).mp hh.1) ((mulForm_spec H _ 0 5 2).mp hh.2))

theorem mulRel_assoc (H : ZFAxioms mem) {x y n a b z : V}
    (hxy : MulRel H x y a) (hyn : MulRel H y n b) (han : MulRel H a n z) :
    MulRel H x b z := by
  let ee : Nat → V := fun _ => vempty H
  have haNat := mulRel_result_nat H hxy
  have h : ∀ k, mem k (omegaV H) →
      Sat mem (scons k (scons x (scons y (scons a ee)))) associativeStage := by
    apply omega_ind H associativeStage (scons x (scons y (scons a ee)))
    · apply (associativeStage_spec H _ x y a ee).mpr
      intro b' z' hb hz
      have eb : b'=vempty H := mulRel_unique H hb (mulRel_zero H hxy.2.1)
      have ez : z'=vempty H := mulRel_unique H hz (mulRel_zero H haNat)
      rw [eb,ez]
      exact mulRel_zero H hxy.1
    · intro k hk ih
      apply (associativeStage_spec H _ x y a ee).mpr
      intro b' z' hb hz
      obtain ⟨b0,hb0⟩ := mulRel_total H hxy.2.1 hk
      obtain ⟨z0,hz0⟩ := mulRel_total H haNat hk
      have hp := (associativeStage_spec H k x y a ee).mp ih b0 z0 hb0 hz0
      have eb : b'=addValue H b0 y := mulRel_unique H hb (mulRel_succ H hb0)
      have ez : z'=addValue H z0 a := mulRel_unique H hz (mulRel_succ H hz0)
      rw [eb,ez]
      exact mulRel_distrib_left H
        (addValue_rel H (mulRel_result_nat H hb0) hxy.2.1) hp hxy
        (addValue_rel H (mulRel_result_nat H hz0) haNat)
  exact (associativeStage_spec H n x y a ee).mp (h n hyn.2.1) b z hyn han

theorem mulRel_assoc_iff (H : ZFAxioms mem) {x y n a b z : V}
    (hxy : MulRel H x y a) (hyn : MulRel H y n b) :
    MulRel H a n z ↔ MulRel H x b z := by
  constructor
  · exact mulRel_assoc H hxy hyn
  · intro hxb
    exact mulRel_comm H
      (mulRel_assoc H (mulRel_comm H hyn) (mulRel_comm H hxy) (mulRel_comm H hxb))

def multiplicationAssociativeForm : Form := sealF
  (fAll (fAll (fAll (fAll (fAll (fAll
    (fImp (fAnd (mulForm 2 5 4) (fAnd (mulForm 1 4 3) (mulForm 0 2 3)))
      (mulForm 0 5 1))))))))

theorem sentence_multiplicationAssociativeForm : Sentence multiplicationAssociativeForm := Sentence_seal _

theorem zfc_proves_multiplication_associative : BProv ZFCax_s [] multiplicationAssociativeForm := by
  apply completeness_inf_context ZFCax_s [] _ Sentences_ZFC
  intro Dom m v hmodel _
  let H := ObjectMultiplication.axioms_of_zfc_model v hmodel
  apply (seal_valid (mem := m) _).mpr ?_ v
  intro ee x y n a b z h
  exact (mulForm_spec H _ 0 5 1).mpr
    (mulRel_assoc H ((mulForm_spec H _ 2 5 4).mp h.1)
      ((mulForm_spec H _ 1 4 3).mp h.2.1) ((mulForm_spec H _ 0 2 3).mp h.2.2))

def distributiveForm : Form := sealF
  (fAll (fAll (fAll (fAll (fAll (fAll (fAll
    (fImp (fAnd (addForm 3 5 4) (fAnd (mulForm 2 6 5)
      (fAnd (mulForm 1 6 4) (addForm 0 2 1)))) (mulForm 0 6 3)))))))))

theorem sentence_distributiveForm : Sentence distributiveForm := Sentence_seal _

theorem zfc_proves_distributivity : BProv ZFCax_s [] distributiveForm := by
  apply completeness_inf_context ZFCax_s [] _ Sentences_ZFC
  intro Dom m v hmodel _
  let H := ObjectMultiplication.axioms_of_zfc_model v hmodel
  apply (seal_valid (mem := m) _).mpr ?_ v
  intro ee x y n a b c d h
  exact (mulForm_spec H _ 0 6 3).mpr
    (mulRel_distrib_left H ((addForm_spec H _ 3 5 4).mp h.1)
      ((mulForm_spec H _ 2 6 5).mp h.2.1) ((mulForm_spec H _ 1 6 4).mp h.2.2.1)
      ((addForm_spec H _ 0 2 1).mp h.2.2.2))

end DiophantineConsistency.ObjectDistributivity
