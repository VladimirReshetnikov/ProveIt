import OAI.Combinatorics.Progressions.Polynomial.CurrentPolynomialDerivativeRemoval
import OAI.Combinatorics.Progressions.Polynomial.PolynomialLiftMatching

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {μ σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem formal_current_derivative_advance
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) (j : ℕ)
    (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hA : ∀ α, coefficients A.coord α ∈ F.realification.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.realification.layer j)
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hvanish : ∀ i α, coefficients
        (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
          (dualAdjoint A⁻¹ (small i - formalLogDerivative i A))) α ∈ V ∧
      coefficients (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
          (dualAdjoint B (rational i) - formalLogDerivative i B)) α ∈ V) :
    ∀ i α,
      coefficients (dualAdjoint A⁻¹ (small i - formalLogDerivative i A)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule ∧
      coefficients (dualAdjoint B (rational i) - formalLogDerivative i B) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  let W := V.restrictScalars ℚ ⊔ F.realification.layer j
  have hWiff (x : ℝ ⊗[ℚ] L) : x ∈ W ↔ x ∈ V ⊔ (F.realLayer j).toSubmodule := by
    change x ∈ V.restrictScalars ℚ ⊔ (F.realLayer j).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  have advance (x : ℝ ⊗[ℚ] L) (hx : x ∈ W)
      (hπ : basisGradeProjection (b.baseChange ℝ) w j x ∈ V) :
      x ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    have hrem := F.real_sub_grade_mem_sup_next b w hlayers V hV j x ((hWiff x).mp hx)
    have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).add_mem hrem (Submodule.mem_sup_left hπ)
    simpa only [sub_add_cancel] using h
  intro i α
  have hpres := polynomial_derivative_removal_preserves_coefficients U W
    (F.realification.invariant_sup_layer U (V.restrictScalars ℚ) hUV j)
    i A B (small i) (rational i) hAU hBU
    (fun β => Submodule.mem_sup_right (hA β)) (fun β => Submodule.mem_sup_right (hB β))
    (fun β => (hWiff _).mpr (hsmall i β)) (fun β => (hWiff _).mpr (hrational i β))
  have hv := hvanish i α
  simp only [coefficients_map, LinearMap.restrictScalars_apply] at hv
  exact ⟨advance _ (hpres.1 α) hv.1, advance _ (hpres.2 α) hv.2⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
