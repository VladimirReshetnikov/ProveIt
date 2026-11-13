import DiophantineConsistency.FoundationPAHFNatSemantics
import ZFCinPA.ValidatorConsistencyEquivalence
import BusyBeaver.ZFC.WFTheory
import BusyBeaver.ZFC.ConstructibleChoice

/-! # A fixed consistency sentence and its standard-natural semantics

The source is Foundation's actual ZFC consistency sentence. Its existing
Gödel–Gentzen image is translated to the PAHF arithmetic syntax, without
changing the source theory or substituting a machine-specific consistency
predicate. The resulting sentence is interpreted only in the standard naturals.

The proof uses the existing PA theorem about the literal C254 validator,
standard-model soundness, and the established external refutation comparisons.
It proves neither an HA comparison with an untranslated proof checker nor a
current-machine/current-equation equivalence in PA or HA.
-/
set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.FoundationZFCConsistencyNat
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open _root_.SetTheory.PA
open _root_.SetTheory.BusyBeaver.ZFC
open LeanProofs.ZFCinPA.ValidatorConsistencyForward254
open LeanProofs.ZFCinPA.ValidatorConsistencyEquivalence
open FoundationPAHFNatSemantics

/-- The actual Foundation theory includes the axiom of choice. -/
noncomputable def sourceSentence : ArithmeticSentence :=
  (LO.FirstOrder.SetTheory.ZermeloFraenkelChoice : LO.FirstOrder.SetTheory).consistent

/-- One explicit, closed PAHF sentence, using the existing GG translation. -/
noncomputable def ggConsistency : Formula :=
  FoundationPAHFSyntax.sentence sourceSentenceᴺ

/-- PA soundness is used here in its standard natural-number model only. -/
theorem source_nat_iff_no_validator :
    sourceSentence.Evalb (M := ℕ) ![] ↔
      ¬∃ code : ℕ, ArithmeticHistory254.value code = 2 := by
  have h := consequence_iff.mp
    (Theory.Proof.sound peano_proves_con_ZFC_iff_validator) ℕ inferInstance
  simp only [LogicalConnective.iff, Semantics.And.models_and,
    Semantics.Imp.models_imply] at h
  have hv : sourceSentence.Evalb (M := ℕ) ![] ↔
      validatorConsistencySentence.Evalb (M := ℕ) ![] := by
    simpa only [sourceSentence, models_iff] using (Iff.intro h.1 h.2)
  exact hv.trans (validatorConsistencySentence_eval (V := ℕ))

/-- Value two is precisely acceptance of the actual falsity code one.
The represented-checker comparison quantifies over every natural code. -/
theorem validator_refutation_iff :
    (∃ code : ℕ, ArithmeticHistory254.value code = 2) ↔
      _root_.SetTheory.BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] _root_.SetTheory.Form.fBot := by
  calc
    _ ↔ ∃ code : ℕ, ArithmeticHistory254.checkDef.val.Evalb ![code, 1] :=
      exists_congr fun code => by
        have h := (ArithmeticHistory254.check_defined (V := ℕ)).df ![code, 1]
        change ArithmeticHistory254.checkDef.val.Evalb ![code, (1 : ℕ)] ↔
          ArithmeticHistory254.value code = (1 : ℕ) + 1 at h
        exact h.symm
    _ ↔ Code254.C254 Code254.F := by
      simpa only [Code254.F] using (ArithmeticHistory254.c254_iff_represented 1).symm
    _ ↔ _root_.SetTheory.BProv _root_.SetTheory.ZFax_s [] _root_.SetTheory.Form.fBot :=
      WFTheory.c254_refutation_iff_zf
    _ ↔ _ := ConstructibleChoice.zf_refutation_iff_zfc_refutation

theorem source_nat_iff_no_refutation :
    sourceSentence.Evalb (M := ℕ) ![] ↔
      ¬ _root_.SetTheory.BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] _root_.SetTheory.Form.fBot :=
  source_nat_iff_no_validator.trans (not_congr validator_refutation_iff)

/-- Unconditional standard-Nat semantics for the fixed translated sentence.
The arbitrary valuation makes the closed-sentence interpretation explicit. -/
theorem ggConsistency_nat (ee : ℕ → ℕ) :
    Formula.Sat natStructure ee ggConsistency ↔
      ¬ _root_.SetTheory.BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] _root_.SetTheory.Form.fBot :=
  (sat_sentence_GG sourceSentence ee).trans source_nat_iff_no_refutation

theorem ggConsistency_environment (ee ff : ℕ → ℕ) :
    Formula.Sat natStructure ee ggConsistency ↔
      Formula.Sat natStructure ff ggConsistency :=
  (ggConsistency_nat ee).trans (ggConsistency_nat ff).symm

end DiophantineConsistency.FoundationZFCConsistencyNat
