import DiophantineConsistency.FoundationHAConsistencySemantics

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAConsistencySemanticsChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open SetTheory.PA HA FoundationZFCConsistencyNat FoundationHAConsistencyNormalization
open FoundationPAHFNatSemantics FoundationHAConsistencySemantics

example : sourceSentence = ∼rho := rfl
example : ordinaryConsistency = .imp ordinaryRefutation .bot := rfl
example : Formula.Sentence ordinaryRefutation := ordinary_refutation_sentence
example : Formula.Sentence ordinaryConsistency := ordinary_consistency_sentence
example (k : Nat) : ¬ Formula.Free k ordinaryRefutation := ordinary_refutation_sentence k
example (k : Nat) : ¬ Formula.Free k ordinaryConsistency := ordinary_consistency_sentence k

example {α : Type*} (M : PreModel α) (ee ff : Nat → α) :
    Formula.Sat M ee ordinaryConsistency ↔ Formula.Sat M ff ordinaryConsistency :=
  ordinary_consistency_environment M ee ff

example (ee : Nat → Nat) :
    Formula.Sat natStructure ee ordinaryRefutation ↔ rho.Evalb (M := Nat) ![] :=
  ordinary_refutation_nat ee
example (ee : Nat → Nat) :
    Formula.Sat natStructure ee ordinaryConsistency ↔
      ¬ _root_.SetTheory.BProv LeanProofs.BoundedZFCConsistency.ZFCax_s []
        _root_.SetTheory.Form.fBot := ordinary_consistency_nat ee

-- Only the already accepted normalization supplies this HA proof.
example : Proves (.imp ggConsistency ordinaryConsistency) := gg_to_ordinary

#print axioms ordinary_refutation_sentence
#print axioms ordinary_consistency_sentence
#print axioms ordinary_refutation_environment
#print axioms ordinary_consistency_environment
#print axioms ordinary_refutation_nat
#print axioms ordinary_consistency_source_nat
#print axioms ordinary_consistency_nat
end DiophantineConsistency.FoundationHAConsistencySemanticsChecks
