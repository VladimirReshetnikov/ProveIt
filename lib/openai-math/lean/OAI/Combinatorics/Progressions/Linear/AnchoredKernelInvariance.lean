import OAI.Combinatorics.Progressions.Estimates.PositiveShiftProductData

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {ι J : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem refiltered_product_kernel_invariant (a : ι)
    (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
    (eta : J → ∀ i, L i →ₗ[ℚ] ℚ) (S : (D a).Space → ℂ)
    (hinvariant : ∀ z, z ∈ (D a).filtration.realification.subgroup s →
      (∀ j, realifyFunctional (eta j a) z.coord = 0) → ∀ x, S (z • x) = S x)
    (hfrequency : ∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W s →
      realifyFunctional (piFrequency (eta j)) x = 0)
    (z : (pi D).RealGroup) (hz : z.coord ∈ (pi D).filtration.realGradedRefiltrationLayer W s)
    (hkernel : ∀ i, i ≠ a → productProjectionHom D i z = 1) (x : (D a).Space) :
    S (productProjectionHom D a z • x) = S x := by
  have htop : z ∈ (pi D).filtration.realification.subgroup s :=
    (pi D).filtration.realGradedRefiltrationLayer_le W s hz
  apply hinvariant _ (productProjectionHom_mem_layer D a s z htop) _ x
  intro j
  apply realify_component_zero_of_piFrequency_zero (eta j) a z.coord (hfrequency j z.coord hz)
  intro i hi
  have h := congrArg NilpotentLieBCHGroup.coord (hkernel i hi)
  simpa only [productProjectionHom, NilpotentLieBCHGroup.realificationMap_coord,
    NilpotentLieBCHGroup.coord_one] using h

theorem refiltered_product_pullback_invariant (a : ι)
    (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
    (eta : J → ∀ i, L i →ₗ[ℚ] ℚ) (S : (D a).Space → ℂ)
    (hinvariant : ∀ z, z ∈ (D a).filtration.realification.subgroup s →
      (∀ j, realifyFunctional (eta j a) z.coord = 0) → ∀ x, S (z • x) = S x)
    (hfrequency : ∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W s →
      realifyFunctional (piFrequency (eta j)) x = 0)
    (z : (pi D).RealGroup) (hz : z.coord ∈ (pi D).filtration.realGradedRefiltrationLayer W s)
    (hkernel : ∀ i, i ≠ a → productProjectionHom D i z = 1) (x : (pi D).Space) :
    S (productProjection D a (z • x)) = S (productProjection D a x) := by
  rw [productProjection_smul]
  exact refiltered_product_kernel_invariant D a W eta S hinvariant hfrequency z hz hkernel _

theorem refiltered_top_commutes
    (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
    (z : (pi D).RealGroup) (hz : z.coord ∈ (pi D).filtration.realGradedRefiltrationLayer W s)
    (g : (pi D).RealGroup) : Commute z g :=
  (pi D).filtration.realification.top_commutes z
    ((pi D).filtration.realGradedRefiltrationLayer_le W s hz) g

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {J : Type*} [Fintype J] {L : (Bool ⊕ (J × Bool)) → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : (Bool ⊕ (J × Bool)) → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
  (eta : J → L (.inl true) →ₗ[ℚ] ℚ) (theta : J → L (.inl false) →ₗ[ℚ] ℚ)
  (alpha : ∀ j, L (.inr (j, true)) →ₗ[ℚ] ℚ) (beta : ∀ j, L (.inr (j, false)) →ₗ[ℚ] ℚ)
  (hfrequency : ∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W s →
    realifyFunctional (piFrequency
      (selectedOrbitFrequencies (anchoredFrequencyData eta theta alpha beta j) (anchoredInputs j))) x = 0)

include hfrequency

theorem anchored_kernel_frequency_zero
    (z : (pi D).RealGroup) (hz : z.coord ∈ (pi D).filtration.realGradedRefiltrationLayer W s)
    (hkernel : ∀ i, i ≠ .inl true → productProjectionHom D i z = 1) (j : J) :
    realifyFunctional (eta j) (productProjectionHom D (.inl true) z).coord = 0 := by
  have h := realify_component_zero_of_piFrequency_zero
    (selectedOrbitFrequencies (anchoredFrequencyData eta theta alpha beta j) (anchoredInputs j))
    (.inl true) z.coord (hfrequency j z.coord hz) (fun i hi => by
      have hk := congrArg NilpotentLieBCHGroup.coord (hkernel i hi)
      simpa only [productProjectionHom, NilpotentLieBCHGroup.realificationMap_coord,
        NilpotentLieBCHGroup.coord_one] using hk)
  simpa [selectedOrbitFrequencies, anchoredFrequencyData, anchoredInputs,
    productProjectionHom, NilpotentLieBCHGroup.realificationMap_coord] using h

theorem anchored_kernel_observable_invariant
    (S : (D (.inl true)).Space → ℂ)
    (hinvariant : ∀ z, z ∈ (D (.inl true)).filtration.realification.subgroup s →
      (∀ j, realifyFunctional (eta j) z.coord = 0) → ∀ x, S (z • x) = S x)
    (z : (pi D).RealGroup) (hz : z.coord ∈ (pi D).filtration.realGradedRefiltrationLayer W s)
    (hkernel : ∀ i, i ≠ .inl true → productProjectionHom D i z = 1)
    (x : (D (.inl true)).Space) :
    S (productProjectionHom D (.inl true) z • x) = S x := by
  apply hinvariant _ (productProjectionHom_mem_layer D (.inl true) s z
    ((pi D).filtration.realGradedRefiltrationLayer_le W s hz))
  exact anchored_kernel_frequency_zero D W eta theta alpha beta hfrequency z hz hkernel

theorem anchored_frozen_observable_invariant
    (S : (D (.inl true)).Space → ℂ)
    (hinvariant : ∀ z, z ∈ (D (.inl true)).filtration.realification.subgroup s →
      (∀ j, realifyFunctional (eta j) z.coord = 0) → ∀ x, S (z • x) = S x)
    (E R b z : (pi D).RealGroup)
    (hz : z.coord ∈ (pi D).filtration.realGradedRefiltrationLayer W s)
    (hkernel : ∀ i, i ≠ .inl true → productProjectionHom D i z = 1) :
    S (QuotientGroup.mk (productProjectionHom D (.inl true) (E * (z * b) * R))) =
      S (QuotientGroup.mk (productProjectionHom D (.inl true) (E * b * R))) := by
  have hcommute := refiltered_top_commutes D W z hz E
  have heq : E * (z * b) * R = z * (E * b * R) := by
    calc
      E * (z * b) * R = (E * z) * b * R := by simp only [mul_assoc]
      _ = (z * E) * b * R := by rw [hcommute.eq]
      _ = z * (E * b * R) := by simp only [mul_assoc]
  rw [heq, map_mul]
  exact anchored_kernel_observable_invariant D W eta theta alpha beta hfrequency S hinvariant
    z hz hkernel (QuotientGroup.mk (productProjectionHom D (.inl true) (E * b * R)))

end Erdos3.RationalFilteredNilmanifold

end

end OAI
