import OAI.Combinatorics.Progressions.Polynomial.RefilteredPolynomialProjection

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {L σ ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (W : LieSubalgebra ℚ F.AssociatedGraded)
  (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem native_refiltered_symbol_conditions
    (q : (F.gradedRefiltration W).realification.PolynomialOrbit w)
    (middle : (F.realification.adaptedPolynomialFiltration w).Group)
    (hmap : VectorPolynomial.map
      (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
      q.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) :
    (F.realPolynomialSymbolHom b ω hF w middle).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W) ∧
    coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈
      F.realGradedRefiltrationLayer W 1 := by
  have hcoeff : ∀ α,
      coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
        F.realGradedRefiltrationLayer W (Finsupp.weight w α) := by
    intro α
    rw [← hmap, coefficients_map]
    exact (F.mem_native_refiltration_layer W (Finsupp.weight w α) _).mp
      (((F.gradedRefiltration W).realification.adapted_iff_coefficients w q.log).mp
        q.adapted α)
  constructor
  · apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w W _).mpr
    exact (F.real_symbol_values_iff_refiltration_coefficients b ω hF w W middle.coord).mpr hcoeff
  · rw [← hmap, coefficients_map]
    apply (F.mem_native_refiltration_layer W 1 _).mp
    rw [(F.gradedRefiltration W).realification.one_eq_top]
    trivial

end Erdos3.NilpotentLieFiltration

end

end OAI
