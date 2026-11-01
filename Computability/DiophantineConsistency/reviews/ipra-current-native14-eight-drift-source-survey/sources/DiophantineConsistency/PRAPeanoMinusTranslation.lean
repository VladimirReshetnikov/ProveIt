import DiophantineConsistency.PRAPeanoMinusOrderAlgebra

/-! Map every Foundation PA-minus theorem to a theorem of candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPeanoMinusTranslation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAPeanoMinusBasic PRAPeanoMinusAddAssoc
  PRAPeanoMinusDistributivity PRAPeanoMinusMulAssoc PRAPeanoMinusMulComm
  PRAPeanoMinusOrderBasic PRAPeanoMinusOrderAlgebra

/-- Every actual Foundation PA-minus axiom has a closed mapped proof in the candidate theory. -/
theorem PRA_proves_peanoMinusAxiom {σ : Sentence ℒₒᵣ} (h : 𝗣𝗔⁻ σ) :
    PRA ⊢ Semiformula.lMap embedding σ := by
  cases h with
  | equal φ hp => exact PRA_proves_equality hp
  | addZero => exact PRA_proves_addZero
  | addAssoc => exact PRA_proves_addAssoc
  | addComm => exact PRA_proves_addComm
  | addEqOfLt => exact PRA_proves_addEqOfLt
  | zeroLe => exact PRA_proves_zeroLe
  | zeroLtOne => exact PRA_proves_zeroLtOne
  | oneLeOfZeroLt => exact PRA_proves_oneLeOfZeroLt
  | addLtAdd => exact PRA_proves_addLtAdd
  | mulZero => exact PRA_proves_mulZero
  | mulOne => exact PRA_proves_mulOne
  | mulAssoc => exact PRA_proves_mulAssoc
  | mulComm => exact PRA_proves_mulComm
  | mulLtMul => exact PRA_proves_mulLtMul
  | distr => exact PRA_proves_distr
  | ltIrrefl => exact PRA_proves_ltIrrefl
  | ltTrans => exact PRA_proves_ltTrans
  | ltTri => exact PRA_proves_ltTri

/-- Every PA-minus theorem has a candidate-PRA proof of its mapped sentence.
The proof uses first-order soundness and completeness in the Lean metatheory. -/
theorem PRA_proves_peanoMinusTheorem {σ : Sentence ℒₒᵣ} (h : 𝗣𝗔⁻ ⊢ σ) :
    PRA ⊢ Semiformula.lMap embedding σ := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  letI : Structure ℒₒᵣ M := (inferInstance : Structure language M).lMap embedding
  have hPA : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := by
    constructor
    intro φ hφ
    have hp := PRA_proves_peanoMinusAxiom hφ
    have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hp
    exact Semiformula.models_lMap.mp hm
  have hσ := models_of_provable hPA h
  exact Semiformula.models_lMap.mpr hσ

end DiophantineConsistency.PRAPeanoMinusTranslation
