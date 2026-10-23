import DiophantineConsistency.ObjectConsistency
import DiophantineConsistency.ObjectArithmetic

/-!
# Universal-closure iteration on internal formula codes

This is the iteration component of an eventual internal `sealF` operation.
Its number of binders ranges over the model's entire omega. Computing the
particular `bound` used by `sealF`, and transporting proof certificates between
sealed and unsealed axiom conventions, are separate outstanding obligations.
-/

namespace DiophantineConsistency.ObjectCodeClosure

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency
open ObjectArithmetic

set_option maxRecDepth 12000

universe u
variable {V : Type u} {mem : V → V → Prop}

private theorem allCode_spec (H : ZFAxioms mem) (ee : Nat → V) (z a : V) :
    relOf mem (fTagUnF 0 6 1) ee z a ↔ z = allCodeV H a :=
  fTagUnF_spec H (scons z (scons a ee)) 0 6 1

/-- Internal iteration of the universal-quantifier code constructor. -/
def CloseCodeRel (H : ZFAxioms mem) (a n c : V) : Prop :=
  ThetaG H (allCodeV H) a c n

/-- Slot `c` is the result of placing `n` universal binders around code `a`. -/
def closeCodeForm (c a n : Nat) : Form :=
  fEx (fAnd (isOmegaForm 0)
    (fThetaG (fTagUnF 0 6 1) (c + 1) (n + 1) (a + 1) 0 1))

theorem closeCodeForm_spec (H : ZFAxioms mem) (ee : Nat → V) (c a n : Nat) :
    Sat mem ee (closeCodeForm c a n) ↔ CloseCodeRel H (ee a) (ee n) (ee c) := by
  constructor
  · rintro ⟨w, hw, h⟩
    have hw' : w = omegaV H := (isOmegaForm_spec H (scons w ee) 0).mp hw
    exact (fThetaG_spec H (fTagUnF 0 6 1) ee (allCodeV H) (allCode_spec H ee)
      (ee a) (scons w ee) (c + 1) (n + 1) (a + 1) 0 1
      (fun _ => rfl) rfl hw').mp h
  · intro h
    refine ⟨omegaV H, (isOmegaForm_spec H _ 0).mpr rfl, ?_⟩
    exact (fThetaG_spec H (fTagUnF 0 6 1) ee (allCodeV H) (allCode_spec H ee)
      (ee a) (scons (omegaV H) ee) (c + 1) (n + 1) (a + 1) 0 1
      (fun _ => rfl) rfl rfl).mpr h

theorem closeCodeRel_total (H : ZFAxioms mem) (a : V) {n : V}
    (hn : mem n (omegaV H)) : ∃ c, CloseCodeRel H a n c :=
  thetaG_total H (fTagUnF 0 6 1) (fun _ => vempty H) (allCodeV H)
    (allCode_spec H _) a n hn

theorem closeCodeRel_unique (H : ZFAxioms mem) {a n c c' : V}
    (h : CloseCodeRel H a n c) (h' : CloseCodeRel H a n c') : c = c' :=
  thetaG_unique H (allCodeV H) a h h'

theorem closeCodeRel_zero (H : ZFAxioms mem) (a : V) :
    CloseCodeRel H a (vempty H) a := thetaG_zero H (allCodeV H) a

theorem closeCodeRel_succ (H : ZFAxioms mem) {a n c : V}
    (h : CloseCodeRel H a n c) :
    CloseCodeRel H a (vsucc H n) (allCodeV H c) :=
  thetaG_succ H (allCodeV H) a h.1 h

/-- The definable iteration packaged as a set-theoretic value. -/
noncomputable def closeCodeValue (H : ZFAxioms mem) (a n : V) : V :=
  applyV H (recFun H (fTagUnF 0 6 1) (fun _ => vempty H) (allCodeV H)
    (allCode_spec H _) a) n

theorem closeCodeValue_spec (H : ZFAxioms mem) (a : V) {n : V}
    (hn : mem n (omegaV H)) : CloseCodeRel H a n (closeCodeValue H a n) :=
  recFun_apply_theta H (fTagUnF 0 6 1) (fun _ => vempty H) (allCodeV H)
    (allCode_spec H _) a hn

private def stageCodeForm : Form :=
  fAll (fImp (closeCodeForm 0 2 1) (fIsFormCodeF 0))

private theorem stageCodeForm_spec (H : ZFAxioms mem) (n a : V) (ee : Nat → V) :
    Sat mem (scons n (scons a ee)) stageCodeForm ↔
      ∀ c, CloseCodeRel H a n c → IsFormCodeSem H c := by
  constructor
  · intro h c hc
    exact (fIsFormCodeF_spec H _ 0).mp
      (h c ((closeCodeForm_spec H _ 0 2 1).mpr hc))
  · intro h c hc
    exact (fIsFormCodeF_spec H _ 0).mpr
      (h c ((closeCodeForm_spec H _ 0 2 1).mp hc))

/-- Formula-code preservation for every internal number of binders. The
induction predicate is the displayed object formula `stageCodeForm`. -/
theorem closeCodeRel_isFormCode (H : ZFAxioms mem) {a n c : V}
    (ha : IsFormCodeSem H a) (h : CloseCodeRel H a n c) : IsFormCodeSem H c := by
  let ee : Nat → V := fun _ => vempty H
  have hind : ∀ k, mem k (omegaV H) →
      Sat mem (scons k (scons a ee)) stageCodeForm := by
    apply omega_ind H stageCodeForm (scons a ee)
    · apply (stageCodeForm_spec H (vempty H) a ee).mpr
      intro c hc
      have he := closeCodeRel_unique H hc (closeCodeRel_zero H a)
      simpa only [he] using ha
    · intro k hk ih
      apply (stageCodeForm_spec H (vsucc H k) a ee).mpr
      intro c hc
      obtain ⟨b, hb⟩ := closeCodeRel_total H a hk
      have hbCode := (stageCodeForm_spec H k a ee).mp ih b hb
      have he := closeCodeRel_unique H hc (closeCodeRel_succ H hb)
      rw [he]
      exact allCodeV_isFormCodeSem H hbCode
  exact (stageCodeForm_spec H n a ee).mp (hind n h.1) c h

private theorem closeN_succ_eq (n : Nat) (f : Form) :
    closeN (n + 1) f = fAll (closeN n f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [closeN, ih]
    rfl

/-- Exact quotation agreement with the existing external `closeN` syntax. -/
theorem closeCodeRel_quotation (H : ZFAxioms mem) (n : Nat) (f : Form) :
    CloseCodeRel H (formCode H f) (natV H n) (formCode H (closeN n f)) := by
  induction n with
  | zero => exact closeCodeRel_zero H _
  | succ n ih =>
    simpa only [natV_succ, closeN_succ_eq, formCode, allCodeV] using closeCodeRel_succ H ih

theorem closeCodeValue_quotation (H : ZFAxioms mem) (n : Nat) (f : Form) :
    closeCodeValue H (formCode H f) (natV H n) = formCode H (closeN n f) :=
  closeCodeRel_unique H (closeCodeValue_spec H _ (natV_mem_omega H n))
    (closeCodeRel_quotation H n f)

/-- The iteration component agrees with `sealF` at its prescribed numeral
bound. The arbitrary-code computation of that bound is not supplied here. -/
theorem closeCodeValue_seal_quotation (H : ZFAxioms mem) (f : Form) :
    closeCodeValue H (formCode H f) (natV H (bound f)) = formCode H (sealF f) :=
  closeCodeValue_quotation H (bound f) f

def closeCodeTotalForm : Form := sealF
  (fAll (fAll (fImp (fNatF 0) (fEx (closeCodeForm 0 2 1)))))

theorem sentence_closeCodeTotalForm : Sentence closeCodeTotalForm := Sentence_seal _

def closeCodeUniqueForm : Form := sealF
  (fAll (fAll (fAll (fAll
    (fImp (fAnd (closeCodeForm 1 3 2) (closeCodeForm 0 3 2)) (fEq 1 0))))))

theorem sentence_closeCodeUniqueForm : Sentence closeCodeUniqueForm := Sentence_seal _

theorem zfc_proves_closeCode_total : BProv ZFCax_s [] closeCodeTotalForm := by
  apply completeness_inf_context ZFCax_s [] closeCodeTotalForm Sentences_ZFC
  intro Dom m ee hmodel _
  let H := zfAxioms_of_zfcModel ee hmodel
  apply (seal_valid _).mpr ?_ ee
  intro ee' a n hn
  have hn' : m n (omegaV H) := (fNatF_spec H _ 0).mp hn
  obtain ⟨c, hc⟩ := closeCodeRel_total H a hn'
  exact ⟨c, (closeCodeForm_spec H _ 0 2 1).mpr hc⟩

theorem zfc_proves_closeCode_unique : BProv ZFCax_s [] closeCodeUniqueForm := by
  apply completeness_inf_context ZFCax_s [] closeCodeUniqueForm Sentences_ZFC
  intro Dom m ee hmodel _
  let H := zfAxioms_of_zfcModel ee hmodel
  apply (seal_valid _).mpr ?_ ee
  intro ee' a n c c' h
  exact closeCodeRel_unique H
    ((closeCodeForm_spec H _ 1 3 2).mp h.1)
    ((closeCodeForm_spec H _ 0 3 2).mp h.2)

end DiophantineConsistency.ObjectCodeClosure
