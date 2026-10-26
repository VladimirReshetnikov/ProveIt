import BoundedZFCConsistency.OmegaRecursion
import BoundedZFCConsistency.CodePredicate
import BoundedZFCConsistency.Choice

/-!
# Object-language natural addition inside arbitrary ZF models

This foundational module supplies an actual set-theory `Form` for addition,
with semantics over every model of `ZFAxioms`, including nonstandard models.
It uses the existing definable omega-recursion theorem to iterate successor.
It does not internalize the external consistency equivalence.
-/

namespace DiophantineConsistency.ObjectArithmetic

set_option maxRecDepth 8000

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- The parameter-free formula characterizing the model's own omega. -/
def isOmegaForm (i : Nat) : Form := fSetByF i (fNatF 0)

theorem isOmegaForm_spec (H : ZFAxioms mem) (ee : Nat → V) (i : Nat) :
    Sat mem ee (isOmegaForm i) ↔ ee i = omegaV H :=
  fSetByF_spec H ee i (fNatF 0) (omegaV H)
    (fun x => fNatF_spec H (scons x ee) 0)

private theorem successor_spec (H : ZFAxioms mem) (ee : Nat → V) (y x : V) :
    relOf mem (fSuccF 0 1) ee y x ↔ y = vsucc H x :=
  fSuccF_spec H (scons y (scons x ee)) 0 1

/-- Slot `z` is the result of iterating successor `n` times from slot `x`.
The single extra binder supplies the model's own omega. -/
def successorIterationForm (z n x : Nat) : Form :=
  fEx (fAnd (isOmegaForm 0)
    (fThetaG (fSuccF 0 1) (z + 1) (n + 1) (x + 1) 0 1))

theorem successorIterationForm_spec (H : ZFAxioms mem) (ee : Nat → V) (z n x : Nat) :
    Sat mem ee (successorIterationForm z n x) ↔
      ThetaG H (vsucc H) (ee x) (ee z) (ee n) := by
  constructor
  · rintro ⟨w, hw, h⟩
    have hw' : w = omegaV H := (isOmegaForm_spec H (scons w ee) 0).mp hw
    exact (fThetaG_spec H (fSuccF 0 1) ee (vsucc H) (successor_spec H ee)
      (ee x) (scons w ee) (z + 1) (n + 1) (x + 1) 0 1
      (fun _ => rfl) rfl hw').mp h
  · intro h
    refine ⟨omegaV H, (isOmegaForm_spec H _ 0).mpr rfl, ?_⟩
    exact (fThetaG_spec H (fSuccF 0 1) ee (vsucc H) (successor_spec H ee)
      (ee x) (scons (omegaV H) ee) (z + 1) (n + 1) (x + 1) 0 1
      (fun _ => rfl) rfl rfl).mpr h

/-- Internal natural addition as a relation on the model's sets. -/
def AddRel (H : ZFAxioms mem) (x y z : V) : Prop :=
  mem x (omegaV H) ∧ ThetaG H (vsucc H) x z y

/-- An actual object-language graph of internal addition. -/
def addForm (z x y : Nat) : Form :=
  fAnd (fNatF x) (successorIterationForm z y x)

theorem addForm_spec (H : ZFAxioms mem) (ee : Nat → V) (z x y : Nat) :
    Sat mem ee (addForm z x y) ↔ AddRel H (ee x) (ee y) (ee z) :=
  and_congr (fNatF_spec H ee x) (successorIterationForm_spec H ee z y x)

/-- The addition relation is total at every internal natural input. -/
theorem addRel_total (H : ZFAxioms mem) {x y : V}
    (hx : mem x (omegaV H)) (hy : mem y (omegaV H)) : ∃ z, AddRel H x y z := by
  obtain ⟨z, hz⟩ := thetaG_total H (fSuccF 0 1) (fun _ => vempty H)
    (vsucc H) (successor_spec H _) x y hy
  exact ⟨z, hx, hz⟩

theorem addRel_unique (H : ZFAxioms mem) {x y z z' : V}
    (h : AddRel H x y z) (h' : AddRel H x y z') : z = z' :=
  thetaG_unique H (vsucc H) x h.2 h'.2

theorem addRel_zero (H : ZFAxioms mem) {x : V} (hx : mem x (omegaV H)) :
    AddRel H x (vempty H) x := ⟨hx, thetaG_zero H (vsucc H) x⟩

theorem addRel_succ (H : ZFAxioms mem) {x y z : V} (h : AddRel H x y z) :
    AddRel H x (vsucc H y) (vsucc H z) :=
  ⟨h.1, thetaG_succ H (vsucc H) x h.2.1 h.2⟩

private def stageNaturalForm : Form :=
  fAll (fImp (successorIterationForm 0 1 2) (fNatF 0))

private theorem stageNaturalForm_spec (H : ZFAxioms mem) (n x : V) (ee : Nat → V) :
    Sat mem (scons n (scons x ee)) stageNaturalForm ↔
      ∀ z, ThetaG H (vsucc H) x z n → mem z (omegaV H) := by
  constructor
  · intro h z hz
    exact (fNatF_spec H _ 0).mp
      (h z ((successorIterationForm_spec H _ 0 1 2).mpr hz))
  · intro h z hz
    exact (fNatF_spec H _ 0).mpr
      (h z ((successorIterationForm_spec H _ 0 1 2).mp hz))

/-- Addition remains inside the internal omega; the proof uses definable
internal induction, so it also covers nonstandard natural arguments. -/
theorem addRel_result_nat (H : ZFAxioms mem) {x y z : V} (h : AddRel H x y z) :
    mem z (omegaV H) := by
  let ee : Nat → V := fun _ => vempty H
  have hind : ∀ n, mem n (omegaV H) →
      Sat mem (scons n (scons x ee)) stageNaturalForm := by
    apply omega_ind H stageNaturalForm (scons x ee)
    · apply (stageNaturalForm_spec H (vempty H) x ee).mpr
      intro z hz
      have hz' := thetaG_unique H (vsucc H) x hz (thetaG_zero H (vsucc H) x)
      rw [hz']
      exact h.1
    · intro n hn ih
      apply (stageNaturalForm_spec H (vsucc H n) x ee).mpr
      intro z hz
      obtain ⟨w, hw⟩ := thetaG_total H (fSuccF 0 1) ee (vsucc H)
        (successor_spec H ee) x n hn
      have hwNat := (stageNaturalForm_spec H n x ee).mp ih w hw
      have he := thetaG_unique H (vsucc H) x hz (thetaG_succ H (vsucc H) x hn hw)
      rw [he]
      exact omega_succ H w hwNat
  exact (stageNaturalForm_spec H y x ee).mp (hind y h.2.1) z h.2

/-- On every pair of external numerals, internal addition gives their usual sum. -/
theorem addRel_numerals (H : ZFAxioms mem) (a b : Nat) :
    AddRel H (natV H a) (natV H b) (natV H (a + b)) := by
  induction b with
  | zero => exact addRel_zero H (natV_mem_omega H a)
  | succ b ih => simpa only [Nat.add_succ, natV_succ] using addRel_succ H ih

theorem addRel_numerals_iff (H : ZFAxioms mem) (a b : Nat) (z : V) :
    AddRel H (natV H a) (natV H b) z ↔ z = natV H (a + b) := by
  constructor
  · intro h
    exact addRel_unique H h (addRel_numerals H a b)
  · intro h
    subst z
    exact addRel_numerals H a b

/-- A model of the repository's sealed ZFC theory supplies the six-axiom
bundle used by definable internal omega-recursion. -/
theorem zfAxioms_of_zfc_model {Dom : Type} {m : Dom → Dom → Prop}
    (v : Nat → Dom) (hmodel : ∀ g, ZFCax_s g → Sat m v g) : ZFAxioms m := by
  have hx : ∀ f, ZFax_s f → Sat m v f := fun f hf => hmodel f (Or.inl hf)
  exact
    { ext := bridge_Ext_fwd
        (extract ZFax_s v Ext_form hx (Or.inl rfl))
      sep := bridge_Sep_fwd (fun phi =>
        extract ZFax_s v (Sep_form phi) hx
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨phi, rfl⟩))))))))
      pair := bridge_Pair_fwd
        (extract ZFax_s v Pair_form hx (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      union := bridge_Union_fwd
        (extract ZFax_s v Union_form hx
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      inf := bridge_Inf_fwd v
        (extract ZFax_s v Inf_form hx
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) v)
      repl := bridge_Repl_fwd (fun psi =>
        extract ZFax_s v (Repl_form psi) hx
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨psi, rfl⟩)))))))) }

/-- The object-language totality sentence for natural addition. -/
def additionTotalForm : Form := sealF
  (fAll (fAll (fImp (fAnd (fNatF 1) (fNatF 0)) (fEx (addForm 0 2 1)))))

theorem sentence_additionTotalForm : Sentence additionTotalForm := Sentence_seal _

/-- The object-language functionality sentence for natural addition. -/
def additionUniqueForm : Form := sealF
  (fAll (fAll (fAll (fAll
    (fImp (fAnd (addForm 1 3 2) (addForm 0 3 2)) (fEq 1 0))))))

theorem sentence_additionUniqueForm : Sentence additionUniqueForm := Sentence_seal _

/-- ZFC proves totality of the supplied addition formula, in the actual
first-order natural-deduction calculus. -/
theorem zfc_proves_addition_total : BProv ZFCax_s [] additionTotalForm := by
  apply completeness_inf_context ZFCax_s [] additionTotalForm Sentences_ZFC
  intro Dom m v hmodel _
  let H := zfAxioms_of_zfc_model v hmodel
  apply (seal_valid (mem := m) _).mpr ?_ v
  intro ee x y hxy
  obtain ⟨z, hz⟩ := addRel_total H
    ((fNatF_spec H _ 1).mp hxy.1) ((fNatF_spec H _ 0).mp hxy.2)
  exact ⟨z, (addForm_spec H _ 0 2 1).mpr hz⟩

/-- ZFC proves uniqueness of the supplied addition formula, without a model
existence or consistency assumption. -/
theorem zfc_proves_addition_unique : BProv ZFCax_s [] additionUniqueForm := by
  apply completeness_inf_context ZFCax_s [] additionUniqueForm Sentences_ZFC
  intro Dom m v hmodel _
  let H := zfAxioms_of_zfc_model v hmodel
  apply (seal_valid (mem := m) _).mpr ?_ v
  intro ee x y z z' h
  exact addRel_unique H ((addForm_spec H _ 1 3 2).mp h.1)
    ((addForm_spec H _ 0 3 2).mp h.2)

end DiophantineConsistency.ObjectArithmetic
