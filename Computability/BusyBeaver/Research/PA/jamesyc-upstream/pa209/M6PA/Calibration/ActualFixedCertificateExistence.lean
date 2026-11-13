module
public import M6PA.Theory
public import M6PA.Scheduler.ActualProofCodeComplete
public import M6PA.Scheduler.ActualCheckerStandard
public import Foundation.FirstOrder.Arithmetic.R0.Basic
@[expose] public section

/-! Fixed closed certificate existence by Sigma-one completeness. The proof
parameter and output number are standard host data; this is not an internal
universal completeness assertion for model-valued formulas or proof codes. -/
namespace M6.PA.ActualFixedCertificateExistence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint NativeCalculus.ActualBasis.Code
noncomputable def sentence (a : Nat) : ArithmeticSentence :=
  “∃ code, !verifyGraph ↑(a+1) code”
theorem sentence_sigma (a : Nat) : ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 (sentence a) := by
  simp [sentence]
theorem sentence_nat {a : Nat} (p : NativeCalculus.ActualBasis.Proof a) :
    Nat↓[ℒₒᵣ] ⊧ sentence a := by
  simp [sentence,models_iff,verify_graph,numeral_eq_natCast,natCast_nat]
  refine ⟨certificate p,?_⟩
  rw [ActualCheckerStandard.verify_standard,verify_certificate p]
  rfl
theorem pa_proves_fixed {a : Nat} (p : NativeCalculus.ActualBasis.Proof a) :
    theory ⊢ sentence a :=
  Arithmetic.sigma_one_completeness (sentence_sigma a) (sentence_nat p)

/-- Only the one fixed standard conclusion is transferred to arbitrary models. -/
theorem fixed_all_models {a : Nat} (p : NativeCalculus.ActualBasis.Proof a)
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory] :
    ∃ code : V, verifyValue code=(a:V)+1 := by
  have h := consequence_iff.mp (Theory.Proof.sound (pa_proves_fixed p)) V inferInstance
  simpa [sentence,models_iff,verify_graph,numeral_eq_natCast,eq_comm] using h
#print axioms sentence_nat
#print axioms pa_proves_fixed
#print axioms fixed_all_models
end M6.PA.ActualFixedCertificateExistence

