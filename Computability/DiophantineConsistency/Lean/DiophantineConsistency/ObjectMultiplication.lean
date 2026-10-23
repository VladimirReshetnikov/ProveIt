import DiophantineConsistency.ObjectArithmetic

/-!
# Internal multiplication by definable iteration of addition

The supplied set-theory formula is interpreted over the internal omega of
arbitrary ZF models. Its correctness is not restricted to external numerals.
Actual ZFC derivations of totality and functionality follow by completeness.
-/

namespace DiophantineConsistency.ObjectMultiplication

set_option maxRecDepth 12000

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency
open ObjectArithmetic

universe u
variable {V : Type u} {mem : V → V → Prop}

private theorem successor_spec (H : ZFAxioms mem) (ee : Nat → V) (y x : V) :
    relOf mem (fSuccF 0 1) ee y x ↔ y = vsucc H x :=
  fSuccF_spec H (scons y (scons x ee)) 0 1

/-- Successor iteration from any seed. At internal-natural arguments this
is the unique result of the already supplied addition relation. -/
noncomputable def addValue (H : ZFAxioms mem) (x y : V) : V :=
  applyV H (recFun H (fSuccF 0 1) (fun _ => vempty H) (vsucc H)
    (successor_spec H _) x) y

theorem addValue_theta (H : ZFAxioms mem) (x : V) {y : V}
    (hy : mem y (omegaV H)) : ThetaG H (vsucc H) x (addValue H x y) y :=
  recFun_apply_theta H (fSuccF 0 1) (fun _ => vempty H) (vsucc H)
    (successor_spec H _) x hy

theorem addValue_rel (H : ZFAxioms mem) {x y : V}
    (hx : mem x (omegaV H)) (hy : mem y (omegaV H)) :
    AddRel H x y (addValue H x y) := ⟨hx, addValue_theta H x hy⟩

theorem addValue_numerals (H : ZFAxioms mem) (a b : Nat) :
    addValue H (natV H a) (natV H b) = natV H (a + b) :=
  (addRel_numerals_iff H a b _).mp
    (addValue_rel H (natV_mem_omega H a) (natV_mem_omega H b))

/-- A definable step adds the parameter in slot `p` to the current value. -/
def incrementForm (p : Nat) : Form := successorIterationForm 0 (p + 2) 1

private theorem increment_spec (H : ZFAxioms mem) (ee : Nat → V) (p : Nat)
    (hp : mem (ee p) (omegaV H)) (y x : V) :
    relOf mem (incrementForm p) ee y x ↔ y = addValue H x (ee p) := by
  change Sat mem (scons y (scons x ee)) (successorIterationForm 0 (p + 2) 1) ↔ _
  rw [successorIterationForm_spec]
  constructor
  · intro h
    exact thetaG_unique H (vsucc H) x h (addValue_theta H x hp)
  · intro h
    subst y
    exact addValue_theta H x hp

/-- The graph of multiplication inside the model's own natural numbers. -/
def MulRel (H : ZFAxioms mem) (x y z : V) : Prop :=
  mem x (omegaV H) ∧
    ThetaG H (fun a => addValue H a x) (vempty H) z y

/-- An actual set-theory formula for natural multiplication.
The two extra binders supply omega and the zero seed. -/
def mulForm (z x y : Nat) : Form :=
  fAnd (fNatF x)
    (fEx (fAnd (isOmegaForm 0)
      (fEx (fAnd (fEmptyF 0)
        (fThetaG (incrementForm x) (z + 2) (y + 2) 0 1 2)))))

theorem mulForm_spec (H : ZFAxioms mem) (ee : Nat → V) (z x y : Nat) :
    Sat mem ee (mulForm z x y) ↔ MulRel H (ee x) (ee y) (ee z) := by
  constructor
  · rintro ⟨hx, w, hw, a, ha, h⟩
    have hx' := (fNatF_spec H ee x).mp hx
    have hw' : w = omegaV H := (isOmegaForm_spec H (scons w ee) 0).mp hw
    have ha' : a = vempty H := (fEmptyF_spec H (scons a (scons w ee)) 0).mp ha
    refine ⟨hx', ?_⟩
    exact (fThetaG_spec H (incrementForm x) ee (fun a => addValue H a (ee x))
      (increment_spec H ee x hx') (vempty H) (scons a (scons w ee))
      (z + 2) (y + 2) 0 1 2 (fun _ => rfl) ha' hw').mp h
  · rintro ⟨hx, h⟩
    refine ⟨(fNatF_spec H ee x).mpr hx, omegaV H,
      (isOmegaForm_spec H _ 0).mpr rfl, vempty H, (fEmptyF_spec H _ 0).mpr rfl, ?_⟩
    exact (fThetaG_spec H (incrementForm x) ee (fun a => addValue H a (ee x))
      (increment_spec H ee x hx) (vempty H) (scons (vempty H) (scons (omegaV H) ee))
      (z + 2) (y + 2) 0 1 2 (fun _ => rfl) rfl rfl).mpr h

/-- Multiplication is total at every internal natural input. -/
theorem mulRel_total (H : ZFAxioms mem) {x y : V}
    (hx : mem x (omegaV H)) (hy : mem y (omegaV H)) : ∃ z, MulRel H x y z := by
  obtain ⟨z, hz⟩ := thetaG_total H (incrementForm 0) (fun _ => x)
    (fun a => addValue H a x) (increment_spec H (fun _ => x) 0 hx) (vempty H) y hy
  exact ⟨z, hx, hz⟩

theorem mulRel_unique (H : ZFAxioms mem) {x y z z' : V}
    (h : MulRel H x y z) (h' : MulRel H x y z') : z = z' :=
  thetaG_unique H (fun a => addValue H a x) (vempty H) h.2 h'.2

theorem mulRel_zero (H : ZFAxioms mem) {x : V} (hx : mem x (omegaV H)) :
    MulRel H x (vempty H) (vempty H) :=
  ⟨hx, thetaG_zero H (fun a => addValue H a x) (vempty H)⟩

theorem mulRel_succ (H : ZFAxioms mem) {x y z : V} (h : MulRel H x y z) :
    MulRel H x (vsucc H y) (addValue H z x) :=
  ⟨h.1, thetaG_succ H (fun a => addValue H a x) (vempty H) h.2.1 h.2⟩

/-- The usual relational successor equation, using the supplied addition graph. -/
theorem mulRel_succ_of_add (H : ZFAxioms mem) {x y z w : V}
    (h : MulRel H x y z) (ha : AddRel H z x w) : MulRel H x (vsucc H y) w := by
  have he : w = addValue H z x := addRel_unique H ha (addValue_rel H ha.1 h.1)
  rw [he]
  exact mulRel_succ H h

private def stageNaturalForm : Form := fAll (fImp (mulForm 0 2 1) (fNatF 0))

private theorem stageNaturalForm_spec (H : ZFAxioms mem) (n x : V) (ee : Nat → V) :
    Sat mem (scons n (scons x ee)) stageNaturalForm ↔
      ∀ z, MulRel H x n z → mem z (omegaV H) := by
  constructor
  · intro h z hz
    exact (fNatF_spec H _ 0).mp (h z ((mulForm_spec H _ 0 2 1).mpr hz))
  · intro h z hz
    exact (fNatF_spec H _ 0).mpr (h z ((mulForm_spec H _ 0 2 1).mp hz))

/-- Multiplication stays inside the internal omega, by definable induction. -/
theorem mulRel_result_nat (H : ZFAxioms mem) {x y z : V} (h : MulRel H x y z) :
    mem z (omegaV H) := by
  let ee : Nat → V := fun _ => vempty H
  have hind : ∀ n, mem n (omegaV H) →
      Sat mem (scons n (scons x ee)) stageNaturalForm := by
    apply omega_ind H stageNaturalForm (scons x ee)
    · apply (stageNaturalForm_spec H (vempty H) x ee).mpr
      intro z hz
      have he := mulRel_unique H hz (mulRel_zero H h.1)
      rw [he]
      exact vempty_in_omega H
    · intro n hn ih
      apply (stageNaturalForm_spec H (vsucc H n) x ee).mpr
      intro z hz
      obtain ⟨w, hw⟩ := mulRel_total H h.1 hn
      have hwNat := (stageNaturalForm_spec H n x ee).mp ih w hw
      have he := mulRel_unique H hz (mulRel_succ H hw)
      rw [he]
      exact addRel_result_nat H (addValue_rel H hwNat h.1)
  exact (stageNaturalForm_spec H y x ee).mp (hind y h.2.1) z h

/-- Numeralwise agreement with ordinary natural multiplication. -/
theorem mulRel_numerals (H : ZFAxioms mem) (a b : Nat) :
    MulRel H (natV H a) (natV H b) (natV H (a * b)) := by
  induction b with
  | zero => exact mulRel_zero H (natV_mem_omega H a)
  | succ b ih =>
      simpa only [Nat.mul_succ, natV_succ, addValue_numerals] using mulRel_succ H ih

theorem mulRel_numerals_iff (H : ZFAxioms mem) (a b : Nat) (z : V) :
    MulRel H (natV H a) (natV H b) z ↔ z = natV H (a * b) := by
  constructor
  · intro h
    exact mulRel_unique H h (mulRel_numerals H a b)
  · intro h
    subst z
    exact mulRel_numerals H a b

/-- Public model extraction for subsequent object-language arithmetic modules. -/
theorem axioms_of_zfc_model {Dom : Type} {m : Dom → Dom → Prop}
    (v : Nat → Dom) (hmodel : ∀ g, ZFCax_s g → Sat m v g) : ZFAxioms m := by
  have hx : ∀ f, ZFax_s f → Sat m v f := fun f hf => hmodel f (Or.inl hf)
  exact
    { ext := bridge_Ext_fwd (extract ZFax_s v Ext_form hx (Or.inl rfl))
      sep := bridge_Sep_fwd (fun phi => extract ZFax_s v (Sep_form phi) hx
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨phi, rfl⟩))))))))
      pair := bridge_Pair_fwd
        (extract ZFax_s v Pair_form hx (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      union := bridge_Union_fwd
        (extract ZFax_s v Union_form hx (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      inf := bridge_Inf_fwd v (extract ZFax_s v Inf_form hx
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) v)
      repl := bridge_Repl_fwd (fun psi => extract ZFax_s v (Repl_form psi) hx
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨psi, rfl⟩)))))))) }

/-- The closed object-language totality sentence. -/
def multiplicationTotalForm : Form := sealF
  (fAll (fAll (fImp (fAnd (fNatF 1) (fNatF 0)) (fEx (mulForm 0 2 1)))))

theorem sentence_multiplicationTotalForm : Sentence multiplicationTotalForm := Sentence_seal _

/-- The closed object-language functionality sentence. -/
def multiplicationUniqueForm : Form := sealF
  (fAll (fAll (fAll (fAll
    (fImp (fAnd (mulForm 1 3 2) (mulForm 0 3 2)) (fEq 1 0))))))

theorem sentence_multiplicationUniqueForm : Sentence multiplicationUniqueForm := Sentence_seal _

theorem zfc_proves_multiplication_total : BProv ZFCax_s [] multiplicationTotalForm := by
  apply completeness_inf_context ZFCax_s [] multiplicationTotalForm Sentences_ZFC
  intro Dom m v hmodel _
  let H := axioms_of_zfc_model v hmodel
  apply (seal_valid (mem := m) _).mpr ?_ v
  intro ee x y hxy
  obtain ⟨z, hz⟩ := mulRel_total H
    ((fNatF_spec H _ 1).mp hxy.1) ((fNatF_spec H _ 0).mp hxy.2)
  exact ⟨z, (mulForm_spec H _ 0 2 1).mpr hz⟩

theorem zfc_proves_multiplication_unique : BProv ZFCax_s [] multiplicationUniqueForm := by
  apply completeness_inf_context ZFCax_s [] multiplicationUniqueForm Sentences_ZFC
  intro Dom m v hmodel _
  let H := axioms_of_zfc_model v hmodel
  apply (seal_valid (mem := m) _).mpr ?_ v
  intro ee x y z z' h
  exact mulRel_unique H ((mulForm_spec H _ 1 3 2).mp h.1)
    ((mulForm_spec H _ 0 3 2).mp h.2)

end DiophantineConsistency.ObjectMultiplication
