import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRABVPairPolynomial
set_option autoImplicit false
namespace DiophantineConsistency.PRABVPairFamilyBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem bvPair_poly_mono (p s : V) (h : p ≤ s) : (p*p+p)^2 ≤ (s*s+s)^2 := by
  have hm : ⟪0,⟪p,0⟫⟫ ≤ ⟪0,⟪s,0⟫⟫ := pair_le_pair (le_refl 0) (pair_le_pair h (le_refl 0))
  simpa [PRABVPairPolynomial.bvPair_eq] using hm
noncomputable def bvPairMonoBody : ArithmeticSemisentence 2 := “p s. p ≤ s → (p*p+p)² ≤ (s*s+s)²”
theorem bvPairMonoBody_model (e : Fin 2 → V) : (bvPairMonoBody).Eval e Empty.elim := by
  simpa [bvPairMonoBody] using bvPair_poly_mono (e 0) (e 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def bvPairMonoSentence : Sentence language := ∀⁰* Semiformula.lMap embedding bvPairMonoBody
theorem candidate_proves_bv_pair_poly_mono : PRA ⊢ bvPairMonoSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact bvPairMonoBody_model e
end DiophantineConsistency.PRABVPairFamilyBound
