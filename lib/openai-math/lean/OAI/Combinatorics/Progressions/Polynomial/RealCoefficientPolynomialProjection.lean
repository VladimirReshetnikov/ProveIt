import OAI.Combinatorics.Progressions.Linear.RealFirstCoefficientBasis

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def realFirstCoefficientOfPolynomial :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) →ₗ[ℚ] F.RealFirstCoefficientModule w :=
  ((F.realFirstCoefficientBasis b ω hF w).repr.symm.restrictScalars ℚ).toLinearMap.comp
    (supportedCoordinates (b.baseChange ℝ)
      {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 + 1 = ω z.2})

theorem realFirstCoefficientOfPolynomial_coordinate
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (z : FirstCoefficientIndex w ω) :
    (F.realFirstCoefficientBasis b ω hF w).repr
      (F.realFirstCoefficientOfPolynomial b ω hF w p) z =
      (b.baseChange ℝ).repr (coefficients p z.val.1) z.val.2 := by
  change ((F.realFirstCoefficientBasis b ω hF w).repr
    ((F.realFirstCoefficientBasis b ω hF w).repr.symm _)) z = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem realFirstCoefficientOfPolynomial_map (x : F.realShiftedCoefficientSubmodule w 1) :
    F.realFirstCoefficientOfPolynomial b ω hF w (F.realAdaptedPolynomialMap w x.val) =
      F.realFirstCoefficientMap w x := by
  apply (F.realFirstCoefficientBasis b ω hF w).repr.injective
  ext z
  rw [F.realFirstCoefficientOfPolynomial_coordinate, F.realFirstCoefficientBasis_polynomial_coordinate]

theorem realFirstCoefficientOfPolynomial_eq_of_firstJet
    (p q : F.realification.adaptedLieSubalgebra w)
    (hpq : F.realification.filteredFirstJetMap w p = F.realification.filteredFirstJetMap w q) :
    F.realFirstCoefficientOfPolynomial b ω hF w p.val =
      F.realFirstCoefficientOfPolynomial b ω hF w q.val := by
  have hdiff := (F.realification.filteredFirstJetMap_eq_iff w p q).mp hpq
  apply (F.realFirstCoefficientBasis b ω hF w).repr.injective
  ext z
  rw [F.realFirstCoefficientOfPolynomial_coordinate, F.realFirstCoefficientOfPolynomial_coordinate]
  have hc := (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mp (hdiff z.val.1)
    z.val.2 (by have hz := z.property; omega)
  rw [map_sub, Finsupp.sub_apply, map_sub, Finsupp.sub_apply] at hc
  exact sub_eq_zero.mp hc

include b ω hF in
theorem realShiftedCoefficient_mem_iff_tensor (k : ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    x ∈ F.realShiftedCoefficientSubmodule w k ↔
      F.realAdaptedPolynomialTensor w x ∈ F.realification.shiftedPolynomialIdeal w k := by
  rw [F.realShiftedCoefficient_eq_span b ω hF, basis_mem_span_image_iff]
  constructor
  · intro hx α
    apply (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mpr
    intro i hi
    by_cases hai : Finsupp.weight w α ≤ ω i
    · change (b.baseChange ℝ).repr (coefficients (F.realAdaptedPolynomialMap w x) α) i = 0
      rw [F.realAdaptedPolynomialTensor_coordinates w b ω hF x ⟨(α, i), hai⟩]
      exact hx ⟨(α, i), hai⟩ hi
    · exact (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mp
        ((F.realAdaptedPolynomialTensor w x).property α) i hai
  · intro hx z hz
    rw [← F.realAdaptedPolynomialTensor_coordinates w b ω hF x z]
    exact (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mp (hx z.val.1) z.val.2 hz

end Erdos3.NilpotentLieFiltration

end

end OAI
