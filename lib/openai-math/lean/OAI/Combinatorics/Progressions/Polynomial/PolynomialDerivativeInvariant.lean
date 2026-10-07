import OAI.Combinatorics.Progressions.Estimates.ShiftedGradedCalculus

namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

theorem directionalDerivative_mem_coefficientSubmodule (V : Submodule ℚ L)
    (h : σ → ℚ) (P : VectorPolynomial σ ℚ L)
    (hP : ∀ α, coefficients P α ∈ V) :
    ∀ α, coefficients (directionalDerivative h P) α ∈ V := by
  intro α
  rw [coefficients_directionalDerivative]
  exact V.sum_mem (fun i _ => V.smul_mem _ (V.smul_mem _ (hP _)))

end VectorPolynomial

namespace NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem polynomialLogDerivative_mem_of_coefficients
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (A : PolynomialGroup σ hnil)
    (hAU : ∀ α, coefficients A.coord α ∈ U)
    (hAV : ∀ α, coefficients A.coord α ∈ V) (t h : σ → ℚ) :
    polynomialLogDerivative t h A ∈ V := by
  apply dualLogDerivative_mem_of_invariant U V hUV (polynomialFirstJetHom t h A)
  · change dualBaseLinear (dualEvalLie t h A.coord) ∈ U
    rw [dualEvalLie_base]
    exact (eval_mem_iff_coefficients U.toSubmodule A.coord).mpr hAU t
  · change dualTangentLinear (dualEvalLie t h A.coord) ∈ V
    rw [dualEvalLie_tangent]
    exact (eval_mem_iff_coefficients V _).mpr
      (directionalDerivative_mem_coefficientSubmodule V h A.coord hAV) t

omit [Fintype σ] in
theorem polynomialDerivativeSystem_remove (t h : σ → ℚ)
    (A Z C : PolynomialGroup σ hnil) (small rational extra : L)
    (hsystem : polynomialLogDerivative t h Z =
      small + dualAdjoint (polynomialValueHom t Z) rational + extra) :
    polynomialLogDerivative t h (A⁻¹ * Z * C⁻¹) =
      dualAdjoint (polynomialValueHom t A)⁻¹ (small - polynomialLogDerivative t h A) +
        dualAdjoint (polynomialValueHom t (A⁻¹ * Z * C⁻¹))
          (dualAdjoint (polynomialValueHom t C) rational - polynomialLogDerivative t h C) +
        dualAdjoint (polynomialValueHom t A)⁻¹ extra := by
  have hsource : dualLogDerivative (polynomialFirstJetHom t h Z) =
      small + dualAdjoint (dualBaseHom (polynomialFirstJetHom t h Z)) rational + extra := by
    simpa only [polynomialFirstJet_base, polynomialLogDerivative] using hsystem
  have he := dualDerivativeSystem_remove (polynomialFirstJetHom t h A)
    (polynomialFirstJetHom t h Z) (polynomialFirstJetHom t h C) small rational extra hsource
  simpa only [map_mul, map_inv, polynomialFirstJet_base, polynomialLogDerivative] using he

end NilpotentLieBCHGroup

namespace NilpotentLieFiltration

open NilpotentLieBCHGroup VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem polynomial_removal_preserves_derivative_layers
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (A C : PolynomialGroup σ F.lowerCentralSeries_eq_bot)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hCU : ∀ α, coefficients C.coord α ∈ U)
    (hAV : ∀ α, coefficients A.coord α ∈ V) (hCV : ∀ α, coefficients C.coord α ∈ V)
    (t h : σ → ℚ) (small rational : L)
    (hsmall : small ∈ V ⊔ F.layer j) (hrational : rational ∈ V ⊔ F.layer j) :
    dualAdjoint (polynomialValueHom t A)⁻¹ (small - polynomialLogDerivative t h A)
        ∈ V ⊔ F.layer j ∧
      dualAdjoint (polynomialValueHom t C) rational - polynomialLogDerivative t h C
        ∈ V ⊔ F.layer j := by
  have haU : dualBaseLinear (polynomialFirstJetHom t h A).coord ∈ U := by
    change dualBaseLinear (dualEvalLie t h A.coord) ∈ U
    rw [dualEvalLie_base]
    exact (eval_mem_iff_coefficients U.toSubmodule _).mpr hAU t
  have hcU : dualBaseLinear (polynomialFirstJetHom t h C).coord ∈ U := by
    change dualBaseLinear (dualEvalLie t h C.coord) ∈ U
    rw [dualEvalLie_base]
    exact (eval_mem_iff_coefficients U.toSubmodule _).mpr hCU t
  have haV : dualTangentLinear (polynomialFirstJetHom t h A).coord ∈ V := by
    change dualTangentLinear (dualEvalLie t h A.coord) ∈ V
    rw [dualEvalLie_tangent]
    exact (eval_mem_iff_coefficients V _).mpr
      (directionalDerivative_mem_coefficientSubmodule V h A.coord hAV) t
  have hcV : dualTangentLinear (polynomialFirstJetHom t h C).coord ∈ V := by
    change dualTangentLinear (dualEvalLie t h C.coord) ∈ V
    rw [dualEvalLie_tangent]
    exact (eval_mem_iff_coefficients V _).mpr
      (directionalDerivative_mem_coefficientSubmodule V h C.coord hCV) t
  have he := F.derivative_removal_preserves_quotient_layers U V hUV j
    (polynomialFirstJetHom t h A) (polynomialFirstJetHom t h C)
    haU hcU haV hcV small rational hsmall hrational
  simpa only [polynomialFirstJet_base, polynomialLogDerivative] using he

end NilpotentLieFiltration
end Erdos3

end

end OAI
