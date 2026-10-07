import OAI.Combinatorics.Progressions.Estimates.MarkedShiftGeneratorBounds

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ) (a : Fin t → ℚ) (d k l : ℕ)
  (ξ : MarkedShiftQuotient F v w marked t →ₗ[ℚ] ℚ) (η : L →ₗ[ℚ] ℚ)

theorem marked_frequency_realification
    (hξ : ∀ z ∈ markedShiftPolynomialSubmodule F v w marked t d k l,
      ξ (lieQuotientMap (markedShiftSecondIdeal F v w marked t) z) =
        η (markedShiftEval F v w marked t a z))
    (z : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t)
    (hz : z ∈ (markedShiftPolynomialSubmodule F v w marked t d k l).baseChange ℝ) :
    realifyFunctional ξ
        ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ z) =
      realifyFunctional η ((markedShiftEval F v w marked t a).baseChange ℝ z) := by
  have h := realifyFunctional_eq_on_submodule
    (markedShiftPolynomialSubmodule F v w marked t d k l)
    (ξ.comp (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap)
    (η.comp (markedShiftEval F v w marked t a)) hξ z hz
  simpa only [realifyFunctional_comp] using h

theorem marked_frequency_character_eq
    (hξ : ∀ z ∈ markedShiftPolynomialSubmodule F v w marked t d k l,
      ξ (lieQuotientMap (markedShiftSecondIdeal F v w marked t) z) =
        η (markedShiftEval F v w marked t a z))
    (z : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t)
    (hz : z ∈ (markedShiftPolynomialSubmodule F v w marked t d k l).baseChange ℝ) :
    CircleFourier.character ((realifyFunctional ξ
        ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ z) : ℝ) :
          CircleFourier.Circle) =
      CircleFourier.character ((realifyFunctional η
        ((markedShiftEval F v w marked t a).baseChange ℝ z) : ℝ) : CircleFourier.Circle) :=
  congrArg (fun x : ℝ => CircleFourier.character (x : CircleFourier.Circle))
    (marked_frequency_realification F v w marked t a d k l ξ η hξ z hz)

end Erdos3

end

end OAI
