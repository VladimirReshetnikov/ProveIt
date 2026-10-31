import DiophantineConsistency.PRAPairTripleWitnessBound
import DiophantineConsistency.PRAIOpenCompleteness
set_option autoImplicit false
namespace DiophantineConsistency.PRABVPairPolynomial
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem bvPair_eq (p : V) : ⟪0, ⟪p,0⟫⟫ = (p*p+p)^2 := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hp : ⟪p,0⟫ = p*p+p := by simp [pair]
  rw [hp]
  by_cases h : 0 < p*p+p
  · simp [pair,h,pow_two]
  · have he : p*p+p = 0 := le_antisymm (le_of_not_gt h) (zero_le : 0 ≤ p*p+p)
    simp [pair,he,pow_two]
noncomputable def bvPairBody : ArithmeticSemisentence 1 := “p. !pair₃Def ((p*p+p)²) 0 p 0”
theorem bvPairBody_model (e : Fin 1 → V) : (bvPairBody).Eval e Empty.elim := by
  simp [bvPairBody, Semiformula.eval_substs, bvPair_eq]
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def bvPairSentence : Sentence language := ∀⁰* Semiformula.lMap embedding bvPairBody
theorem candidate_proves_bv_pair_polynomial : PRA ⊢ bvPairSentence :=
  PRAIOpenCompleteness.proves_allClosure _ (by
    intro M _ _ e
    exact bvPairBody_model e)

end DiophantineConsistency.PRABVPairPolynomial
