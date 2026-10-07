import OAI.Combinatorics.Progressions.Polynomial.CoefficientPolynomialLift
import OAI.Combinatorics.Progressions.Sampling.AllocatedCoefficientSampler

namespace OAI

section

namespace Erdos3

theorem continuousPolynomialDensity_coefficient_bound {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    {a : J → ℝ} (ha : continuousPolynomialDensity e T P j₀ R σ a ≠ 0) (j : J) :
    |a j| * monomialScale T (e j) ≤ 3 * R / 4 :=
  (scaledCoefficientDensity_coefficient_bound e T hT _ _
    (continuousPolynomialDensity_width_pos P j₀ hR hσ) ha j).trans
      (allocatedProfile_term_bound P j₀ hj₀ hR hσ hσ1 j)

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (hσ1 : ∀ j, σ j ≤ 1)

include hσ1 in
theorem allocatedLayerCoefficient_scaled_bounds (j : Fin m)
    (a : (I j → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℝ) ×
      (Fin (n j) → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ))
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j) (allocatedLayerWidths B U b S j)
      (allocatedLayerIntegerPMFs B U b hR hσ S j) a) (d) :
    (∀ i, |a.1 i d| * monomialScale (layerSamplerBox B U b S) d.val ≤ R j) ∧
      (∀ i, |(a.2 i d : ℝ) / basisAxisScale (b j) i| *
        monomialScale (layerSamplerBox B U b S) d.val ≤ R j) := by
  have hT : ∀ v, 0 < layerSamplerBox B U b S v :=
    fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v)
  have hs := (allocatedArraySupported_iff_rows Subtype.val (layerSamplerBox B U b S)
    (layerContinuousPrincipalSlots B j) (constantCoefficientSlot _ _) (R j) (σ j)
    (allocatedLayerIntegerPMFs B U b hR hσ S j) a).mp ha
  constructor
  · intro i
    exact (continuousPolynomialDensity_coefficient_bound Subtype.val _ hT _ _
      (layerContinuousPrincipalSlots_not_constant B j i) (hR j) (hσ j) (hσ1 j) (hs.1 i) d).trans
        (by linarith [hR j])
  · intro i
    exact (allocatedIntegerCoefficient_bound (layerIntegerPrincipalSlots B j i) (constantCoefficientSlot _ _)
      (j.val + 1) (basisAxisScale (b j) i) S.value (layerTailDegree m) (Nat.zero_lt_succ _) (basisAxisScale_pos (b j) i)
      S.positive (layerSamplerBox B U b S) hT (layerSamplerBox_le B U b S) Subtype.val
      (fun d => d.property.trans (layerDegree_le_tailDegree j))
      (R j) (σ j) (hR j) (hσ j) (hσ1 j) (S.gap j i) (S.width j)
      (layerIntegerPrincipalSlots_not_constant B j i) rfl
      (layerSamplerSides_integer_principal B U b R S.value j i) d (hs.2 i d)).trans (by linarith [hR j])

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)

include hσ1 C hC hchart hsmall

theorem allocatedLayerLiftCoefficient_bound (j : Fin m) (a)
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j) (allocatedLayerWidths B U b S j)
      (allocatedLayerIntegerPMFs B U b hR hσ S j) a) (d) (i : J j) :
    |mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) a d i| ≤
      (1 / 4 : ℝ) / monomialScale (layerSamplerBox B U b S) d.val := by
  have hT : ∀ v, 0 < layerSamplerBox B U b S v :=
    fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v)
  have ha' := allocatedLayerCoefficient_scaled_bounds B U b hR hσ S hσ1 j a ha d
  have hs := monomialScale_pos (layerSamplerBox B U b S) hT d.val
  have hbnd := mixedRealPoint_scaled_coordinate_bound (euclideanSubspace (U j)) (b j) (o j)
    (hC j) (hR j).le hs (hchart j) (fun k => a.1 k d)
    (fun k => (a.2 k d : ℝ) / basisAxisScale (b j) k) ha'.1 ha'.2 i
  exact hbnd.trans (div_le_div_of_nonneg_right (by simpa only [mul_assoc] using hsmall j) hs.le)

theorem allocatedLayerLiftPolynomial_coefficient_bound (j : Fin m) (a)
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j) (allocatedLayerWidths B U b S j)
      (allocatedLayerIntegerPMFs B U b hR hσ S j) a) (α : LayerSamplerVariables G I n B →₀ ℕ) (i : J j) :
    |(mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val a i).coeff α| ≤
      (1 / 4 : ℝ) / monomialScale (layerSamplerBox B U b S) α := by
  exact mixedLiftPolynomial_coefficient_bound _ (b j) (o j) Subtype.val Subtype.val_injective a
    (layerSamplerBox B U b S) (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v))
    (by norm_num) (allocatedLayerLiftCoefficient_bound B U b hR hσ S hσ1 o C hC hchart hsmall j a ha) α i

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (hσ1 : ∀ j, σ j ≤ 1)

include hσ1

theorem allocatedLayerLiftCoefficient_radius_bound
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (j : Fin m) {C : ℝ} (hC : 0 ≤ C)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C * ‖v‖)
    (a) (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) (i : J j) :
    |mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) a d i| ≤
      (C * (((Fintype.card (I j) : ℝ) + 1) * R j)) /
        monomialScale (layerSamplerBox B U b S) d.val := by
  have hT : ∀ v, 0 < layerSamplerBox B U b S v :=
    fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v)
  have h := allocatedLayerCoefficient_scaled_bounds B U b hR hσ S hσ1 j a ha d
  exact mixedRealPoint_scaled_coordinate_bound _ (b j) (o j) hC (hR j).le
    (monomialScale_pos _ hT d.val) hchart _ _ h.1 h.2 i

theorem allocatedLayerLiftPolynomial_radius_bound
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (j : Fin m) {C : ℝ} (hC : 0 ≤ C)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C * ‖v‖)
    (a) (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (α : LayerSamplerVariables G I n B →₀ ℕ) (i : J j) :
    |(mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val a i).coeff α| ≤
      (C * (((Fintype.card (I j) : ℝ) + 1) * R j)) /
        monomialScale (layerSamplerBox B U b S) α := by
  exact mixedLiftPolynomial_coefficient_bound _ (b j) (o j) Subtype.val Subtype.val_injective a
    (layerSamplerBox B U b S)
    (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v))
    (mul_nonneg hC (mul_nonneg (by positivity) (hR j).le))
    (allocatedLayerLiftCoefficient_radius_bound B U b hR hσ S hσ1 o j hC hchart a ha) α i

end Erdos3.VectorPolynomial

end

end OAI
