module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeFiniteSupplier
@[expose] public section
/-! Isolate the sole unpaid original axiom branch without standardizing its
model-valued induction witnesses. The finite26 branch is already supplied. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def originalInductionSupplierSentence : ArithmeticSentence :=
  “∀ p, !((chInd (⊤ : 𝚫ᴬ₁.Semisentence 1)).sigma) p →
    ∃ q, !formulaCodeGraph q 0 p ∧ !(provable Presentation.ordinaryPAeq) q”
theorem originalInductionSupplier_iff :
    V↓[ℒₒᵣ] ⊧ originalInductionSupplierSentence ↔
      ∀p : V, InductionR (fun _=>True) p →
        Provable Presentation.ordinaryPAeq (formulaCode 0 p) := by
  simp [originalInductionSupplierSentence,models_iff,Matrix.comp_vecCons'',chInd,InductionR,
    lt_succ_iff_le,eq_comm]

theorem axiomSupplier_iff_original_induction :
    V↓[ℒₒᵣ] ⊧ axiomSupplierSentence Presentation.ordinaryPAeq ↔
      V↓[ℒₒᵣ] ⊧ originalInductionSupplierSentence := by
  rw [axiomSupplier_iff,originalInductionSupplier_iff]
  constructor
  · intro h p hp
    exact h p (Peano.mem_Δ₁Class_iff.mpr (Or.inr hp))
  · intro h p hp
    rcases Peano.mem_Δ₁Class_iff.mp hp with hf|hi
    · exact finite_axiom_supplier hf
    · exact h p hi

variable [V↓[ℒₒᵣ] ⊧* theory]
theorem derivation_transport_of_original_induction
    (hi : V↓[ℒₒᵣ] ⊧ originalInductionSupplierSentence) {d s : V}
    (hd : DerivationOf theory d s) : Derivable Presentation.ordinaryPAeq (sequentCode s) :=
  derivationOf_transport Presentation.ordinaryPAeq (axiomSupplier_iff_original_induction.mpr hi) hd

theorem refutation_transport_of_original_induction
    (hi : V↓[ℒₒᵣ] ⊧ originalInductionSupplierSentence)
    (hp : Provable theory (qqFalsum : V)) : Provable Presentation.ordinaryPAeq (qqFalsum : V) :=
  refutation_transport Presentation.ordinaryPAeq (axiomSupplier_iff_original_induction.mpr hi) hp

#print axioms originalInductionSupplier_iff
#print axioms axiomSupplier_iff_original_induction
#print axioms derivation_transport_of_original_induction
#print axioms refutation_transport_of_original_induction
end M6.PA.FoundationPAeqCode

