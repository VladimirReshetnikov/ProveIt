import OAI.Combinatorics.Progressions.Fourier.ClearedSectionFrequency
import OAI.Combinatorics.Progressions.Linear.QuotientProjectionCoordinates

namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem subspaceArrayFunctional_integer_section {I S J : Type*}
    [Fintype I] [Fintype S] [Fintype J] [DecidableEq I] [DecidableEq S]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℚ) (T : Matrix I S ℚ)
    (hT : E * T * E = E) (frequency : Matrix I J ℤ)
    (M : (S → U) →ₗ[ℝ] ℝ)
    (hfactor : ∀ x, subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)) x =
      M (matrixModuleAction (fun s i => (E s i : ℝ)) x)) (x : I → U) :
    subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)) x =
      subspaceArrayFunctional U (fun s a => (sectionIntegerFrequency T frequency s a : ℝ))
        (matrixModuleAction (fun s i => (E s i : ℝ)) ((matrixDenominator T : ℝ)⁻¹ • x)) := by
  have hq : (matrixDenominator T : ℝ) ≠ 0 := by
    exact_mod_cast (matrixDenominator_pos T).ne'
  have hreal := real_matrix_image_section E T hT
  have hf := subspaceArrayFunctional_factor_section U
    (fun s i => (E s i : ℝ)) (fun i s => (T i s : ℝ)) hreal
    (fun i a => (frequency i a : ℝ)) M hfactor ((matrixDenominator T : ℝ)⁻¹ • x)
  have hc := congrArg
    (fun B : Matrix S J ℝ => subspaceArrayFunctional U B
      (matrixModuleAction (fun s i => (E s i : ℝ)) ((matrixDenominator T : ℝ)⁻¹ • x)))
    (sectionIntegerFrequency_real T frequency)
  simp only [subspaceArrayFunctional_smul] at hc
  calc
    _ = (matrixDenominator T : ℝ) *
        subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)) ((matrixDenominator T : ℝ)⁻¹ • x) := by
      rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]
    _ = _ := (congrArg (fun r : ℝ => (matrixDenominator T : ℝ) * r) hf).trans hc.symm

end Erdos3

end

end OAI
