import DiophantineConsistency.FoundationHAConsistencyNormalization
import DiophantineConsistency.FoundationPAHFOrdinarySemantics

/-! Closed syntax and standard-Nat meaning of the retained ordinary predicate.
The consistency target uses HA negation outside the actual positive source
provability predicate. Its external Nat meaning is the exact repository
refutation proposition; this is not an HA equivalence with a separate checker
or a current-equation calibration. No broad machine Bridge is imported. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAConsistencySemantics
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open SetTheory.PA HA FoundationZFCConsistencyNat FoundationHAConsistencyNormalization
open FoundationPAHFNatSemantics FoundationPAHFOrdinarySemantics

theorem ordinary_refutation_sentence : Formula.Sentence ordinaryRefutation :=
  ordinary_sentence rho

theorem ordinary_consistency_sentence : Formula.Sentence ordinaryConsistency := by
  intro k hk
  exact hk.elim (ordinary_refutation_sentence k) False.elim

/-- These two invariance results require no arithmetic axioms on the premodel. -/
theorem ordinary_refutation_environment {α : Type*} (M : PreModel α) (ee ff : Nat → α) :
    Formula.Sat M ee ordinaryRefutation ↔ Formula.Sat M ff ordinaryRefutation :=
  Formula.Sat_ext_free M _ (fun k hk => False.elim (ordinary_refutation_sentence k hk))

theorem ordinary_consistency_environment {α : Type*} (M : PreModel α) (ee ff : Nat → α) :
    Formula.Sat M ee ordinaryConsistency ↔ Formula.Sat M ff ordinaryConsistency :=
  Formula.Sat_ext_free M _ (fun k hk => False.elim (ordinary_consistency_sentence k hk))

/-- The positive predicate keeps its actual source formula, without witness
recovery or comparison to an independently encoded proof checker in HA. -/
theorem ordinary_refutation_nat (ee : Nat → Nat) :
    Formula.Sat natStructure ee ordinaryRefutation ↔ rho.Evalb (M := Nat) ![] :=
  sat_ordinary_sentence rho ee

theorem ordinary_consistency_source_nat (ee : Nat → Nat) :
    Formula.Sat natStructure ee ordinaryConsistency ↔
      sourceSentence.Evalb (M := Nat) ![] := by
  rw [source_eq_neg_rho]
  change (¬ Formula.Sat natStructure ee ordinaryRefutation) ↔
    (∼rho).EvalAux _ Empty.elim ![]
  rw [Semiformula.EvalAux_neg]
  exact not_congr (ordinary_refutation_nat ee)

/-- The primary external meaning, stated without importing the broad Bridge.
The accepted source comparison is used only in the standard natural model. -/
theorem ordinary_consistency_nat (ee : Nat → Nat) :
    Formula.Sat natStructure ee ordinaryConsistency ↔
      ¬ _root_.SetTheory.BProv LeanProofs.BoundedZFCConsistency.ZFCax_s []
        _root_.SetTheory.Form.fBot :=
  (ordinary_consistency_source_nat ee).trans source_nat_iff_no_refutation

end DiophantineConsistency.FoundationHAConsistencySemantics
