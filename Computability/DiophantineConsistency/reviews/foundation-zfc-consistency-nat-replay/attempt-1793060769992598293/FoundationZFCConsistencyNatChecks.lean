import DiophantineConsistency.FoundationZFCConsistencyNat

set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.FoundationZFCConsistencyNatChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open _root_.SetTheory.PA
open _root_.SetTheory.BusyBeaver.ZFC
open FoundationPAHFNatSemantics FoundationZFCConsistencyNat

/-- Literal theory and translation bindings, rather than a placeholder predicate. -/
example : sourceSentence =
    ((LO.FirstOrder.SetTheory.ZermeloFraenkelChoice : LO.FirstOrder.SetTheory).consistent :
      ArithmeticSentence) := rfl

example : ggConsistency = FoundationPAHFSyntax.sentence sourceSentenceᴺ := rfl

/-- The accepted result includes the successor tag of falsity code one. -/
example : Code254.F + 1 = (2 : ℕ) := rfl

example : (∃ code : ℕ, ArithmeticHistory254.value code = 2) ↔
    _root_.SetTheory.BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] _root_.SetTheory.Form.fBot :=
  validator_refutation_iff

example (ee : ℕ → ℕ) : Formula.Sat natStructure ee ggConsistency ↔
    ¬ _root_.SetTheory.BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] _root_.SetTheory.Form.fBot :=
  ggConsistency_nat ee

example (ee : ℕ → ℕ)
    (h : _root_.SetTheory.BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] _root_.SetTheory.Form.fBot) :
    ¬ Formula.Sat natStructure ee ggConsistency :=
  fun hSat => (ggConsistency_nat ee).mp hSat h

example : Formula.Sat natStructure (fun _ => 0) ggConsistency ↔
    Formula.Sat natStructure (fun n => n + 7) ggConsistency :=
  ggConsistency_environment _ _

#print axioms LeanProofs.ZFCinPA.ValidatorConsistencyEquivalence.peano_proves_con_ZFC_iff_validator
#print axioms WFTheory.c254_refutation_iff_zf
#print axioms ConstructibleChoice.zf_refutation_iff_zfc_refutation
#print axioms source_nat_iff_no_validator
#print axioms validator_refutation_iff
#print axioms source_nat_iff_no_refutation
#print axioms ggConsistency_nat
#print axioms ggConsistency_environment

end DiophantineConsistency.FoundationZFCConsistencyNatChecks
