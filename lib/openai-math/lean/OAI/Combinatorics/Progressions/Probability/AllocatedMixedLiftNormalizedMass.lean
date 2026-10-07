import OAI.Combinatorics.Progressions.Estimates.AllocatedNormalizedCoefficientBounds
import OAI.Combinatorics.Progressions.Estimates.AllocatedRecoveredPreparedFreeze

namespace OAI

section

namespace Erdos3
open MvPolynomial

theorem scaleMvPolynomialAxes_neg {V : Type*} (T : V → ℝ) (p : MvPolynomial V ℝ) :
    scaleMvPolynomialAxes T (-p) = -scaleMvPolynomialAxes T p := by
  ext α
  simp only [scaleMvPolynomialAxes_coeff, coeff_neg, neg_mul]

theorem normalizedPolynomialMass_neg {V : Type*} (p : MvPolynomial V ℝ) :
    realPolynomialMass (-p) = realPolynomialMass p := by
  simp only [realPolynomialMass, support_neg, coeff_neg, abs_neg]

theorem normalizedAxes_homogeneousComponent_commute {V : Type*}
    (T : V → ℝ) (w : V → ℕ) (n : ℕ) (p : MvPolynomial V ℝ) :
    scaleMvPolynomialAxes T (weightedHomogeneousComponent w n p) =
      weightedHomogeneousComponent w n (scaleMvPolynomialAxes T p) := by
  classical
  ext α
  simp only [scaleMvPolynomialAxes_coeff, coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

theorem normalizedMass_homogeneousComponent_projection_le {V : Type*}
    (w : V → ℕ) (n : ℕ) (p : MvPolynomial V ℝ) :
    realPolynomialMass (weightedHomogeneousComponent w n p) ≤ realPolynomialMass p := by
  classical
  have hs : (weightedHomogeneousComponent w n p).support ⊆ p.support := by
    intro α hα
    rw [mem_support_iff, coeff_weightedHomogeneousComponent] at hα
    split_ifs at hα with h
    · exact mem_support_iff.mpr hα
    · exact False.elim (hα rfl)
  rw [realPolynomialMass_eq_sum_of_support_subset _ _ hs]
  apply Finset.sum_le_sum
  intro α _
  rw [coeff_weightedHomogeneousComponent]
  split_ifs <;> simp only [le_refl, abs_zero, abs_nonneg]

theorem normalizedMass_neg_weightedHomogeneousComponent_le {V : Type*}
    (T : V → ℝ) (w : V → ℕ) (n : ℕ) (p : MvPolynomial V ℝ) :
    realPolynomialMass (scaleMvPolynomialAxes T (-weightedHomogeneousComponent w n p)) ≤
      realPolynomialMass (scaleMvPolynomialAxes T p) := by
  rw [scaleMvPolynomialAxes_neg, normalizedPolynomialMass_neg,
    normalizedAxes_homogeneousComponent_commute]
  exact normalizedMass_homogeneousComponent_projection_le w n _

end Erdos3

end

section

namespace Erdos3
open Module Submodule

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

theorem mixedLiftPolynomial_scaled_coefficients [Fintype V]
    (e : J → V →₀ ℕ) (he : Function.Injective e)
    (a : (I → J → ℝ) × (Fin n → J → ℤ))
    (T : V → ℝ) (hT : ∀ v, 0 < T v) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hc : ∀ i j, |a.1 i j| * monomialScale T (e j) ≤ R)
    (hz : ∀ i j, |(a.2 i j : ℝ) / basisAxisScale b i| * monomialScale T (e j) ≤ R)
    (α : V →₀ ℕ) (d : D) :
    |(mixedLiftPolynomial W b o e a d).coeff α| ≤
      C * (((Fintype.card I : ℝ) + 1) * R) / monomialScale T α := by
  apply mixedLiftPolynomial_coefficient_bound W b o e he a T hT (by positivity)
  intro j d
  exact mixedRealPoint_scaled_coordinate_bound W b o hC hR
    (monomialScale_pos T hT (e j)) hchart _ _ (fun i => hc i j) (fun i => hz i j) d

variable [Fintype V]

theorem mixedLiftPolynomial_scaled_mass
    (e : J → V →₀ ℕ) (he : Function.Injective e)
    (a : (I → J → ℝ) × (Fin n → J → ℤ))
    (T : V → ℝ) (hT : ∀ v, 0 < T v) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hc : ∀ i j, |a.1 i j| * monomialScale T (e j) ≤ R)
    (hz : ∀ i j, |(a.2 i j : ℝ) / basisAxisScale b i| * monomialScale T (e j) ≤ R)
    {s : ℕ} (hdegree : ∀ j, (e j).sum (fun _ k => k) ≤ s) (d : D) :
    realPolynomialMass (scaleMvPolynomialAxes T (mixedLiftPolynomial W b o e a d)) ≤
      ((s + 1 : ℕ) : ℝ) * ((Fintype.card V + 1 : ℕ) : ℝ) ^ s *
        (C * (((Fintype.card I : ℝ) + 1) * R)) := by
  apply (scaleMvPolynomialAxes_mass_le T hT _
    (fun α => mixedLiftPolynomial_scaled_coefficients W b o e he a T hT hC hR
      hchart hc hz α d)).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast polynomial_support_card_le _ (mixedLiftPolynomial_degree W b o e a hdegree d)

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
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (hσ1 : ∀ j, σ j ≤ 1)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)

include hσ1 hC hchart

theorem allocatedLayerSupported_normalized_mass (j : Fin m) (a)
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (i : J j) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val a i)) ≤
      ((j.val + 2 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ (j.val + 1) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * R j)) := by
  have hT : ∀ v, 0 < layerSamplerBox B U b S v :=
    fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v)
  have hs := (allocatedArraySupported_iff_rows Subtype.val (layerSamplerBox B U b S)
    (layerContinuousPrincipalSlots B j) (constantCoefficientSlot _ _) (R j) (σ j)
    (allocatedLayerIntegerPMFs B U b hR hσ S j) a).mp ha
  apply mixedLiftPolynomial_scaled_mass (euclideanSubspace (U j)) (b j) (o j)
    Subtype.val Subtype.val_injective a _ hT (hC j) (hR j).le (hchart j)
  · intro k d
    exact continuousPolynomialDensity_coefficient_le_radius Subtype.val _ hT _ _
      (layerContinuousPrincipalSlots_not_constant B j k) (hR j) (hσ j) (hσ1 j) (hs.1 k) d
  · intro k d
    exact allocatedIntegerCoefficient_le_radius
      (layerIntegerPrincipalSlots B j k) (constantCoefficientSlot _ _)
      (j.val + 1) (basisAxisScale (b j) k) S.value (layerTailDegree m) (Nat.zero_lt_succ _)
      (basisAxisScale_pos (b j) k) S.positive (layerSamplerBox B U b S) hT
      (layerSamplerBox_le B U b S) Subtype.val (fun d => d.property.trans (layerDegree_le_tailDegree j))
      (R j) (σ j) (hR j) (hσ j) (hσ1 j) (S.gap j k) (S.width j)
      (layerIntegerPrincipalSlots_not_constant B j k) rfl
      (layerSamplerSides_integer_principal B U b R S.value j k) d (hs.2 k d)
  · intro d
    exact d.property

theorem allocatedLayerSupported_normalized_top_mass (j : Fin m) (a)
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (i : J j) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (-MvPolynomial.weightedHomogeneousComponent (fun _ => 1) (j.val + 1)
        (mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val a i))) ≤
      ((j.val + 2 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ (j.val + 1) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * R j)) :=
  (normalizedMass_neg_weightedHomogeneousComponent_le _ _ _ _).trans
    (allocatedLayerSupported_normalized_mass B U b o hR hσ S hσ1 C hC hchart j a ha i)

theorem allocatedLayerSupported_normalized_mass_uniform
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (j : Fin m) (a)
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (i : J j) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val a i)) ≤
      ((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m := by
  apply (allocatedLayerSupported_normalized_mass B U b o hR hσ S hσ1 C hC hchart j a ha i).trans
  calc
    _ ≤ ((j.val + 2 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ (j.val + 1) * 1 :=
      mul_le_mul_of_nonneg_left (hsmall j) (by positivity)
    _ ≤ ((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m := by
      rw [mul_one]
      apply mul_le_mul
      · exact_mod_cast (show j.val + 2 ≤ m + 1 by omega)
      · exact pow_le_pow_right₀ (by norm_cast; omega) (by omega)
      · positivity
      · positivity

end Erdos3.VectorPolynomial

end

end OAI
