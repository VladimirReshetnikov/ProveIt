import DiophantineConsistency.FoundationHAZFCValidator

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAZFCValidatorChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open _root_.SetTheory.PA HA FoundationPAHFSyntax
open FoundationZFCConsistencyNat FoundationHAZFCValidator
open LeanProofs.ZFCinPA.ValidatorConsistencyForward254

example : ggValidator = sentence validatorConsistencySentenceᴺ := rfl
example : ggConsistency = sentence
    ((LO.FirstOrder.SetTheory.ZermeloFraenkelChoice : LO.FirstOrder.SetTheory).consistent :
      ArithmeticSentence)ᴺ := rfl

/-- The fixed literal target has an actual HA proof with no source-proof,
stability, model, or checker-equivalence premise. -/
theorem literal_equivalence : Proves (.and
    (.imp ggConsistency (sentence validatorConsistencySentenceᴺ))
    (.imp (sentence validatorConsistencySentenceᴺ) ggConsistency)) :=
  equivalence

example : Proves (.imp ggConsistency ggValidator) := consistency_to_validator
example : Proves (.imp ggValidator ggConsistency) := validator_to_consistency

#print axioms LeanProofs.ZFCinPA.ValidatorConsistencyEquivalence.peano_proves_con_ZFC_iff_validator
#print axioms FoundationHAPeano.peano_provable
#print axioms FoundationHACurrentTransfer.sentence_imp_elim
#print axioms translated_equivalence
#print axioms consistency_to_validator
#print axioms validator_to_consistency
#print axioms equivalence
#print axioms literal_equivalence
end DiophantineConsistency.FoundationHAZFCValidatorChecks
