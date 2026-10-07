import OAI.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m L : ℕ} {X : Type*} [Fintype X]
    {I : Fin m → Type*} {n : Fin m → ℕ}

theorem allocatedSmoothRankCoefficientIndex_card_le (hm : 0 < m)
    (inactive : LayerSamplerAxis I n → Prop) :
    Fintype.card (AllocatedSmoothRankCoefficientIndex X inactive L) ≤
      L * (Fintype.card X + ∑ j : Fin m, n j) := by
  have hcount (j : Fin m) : Fintype.card (AllocatedCongruenceIntegerAxis inactive j) ≤ n j := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le
      (fun i : Fin (n j) => ¬ inactive ⟨j, Sum.inr i⟩)
  change Fintype.card (Σ j : Fin m,
    (SpatialDegreeOutput X j ⊕ AllocatedCongruenceIntegerAxis inactive j) × Fin L) ≤ _
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  calc
    _ ≤ ∑ j : Fin m, (Fintype.card (SpatialDegreeOutput X j) + n j) * L :=
      Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_right L (Nat.add_le_add_left (hcount j) _))
    _ = L * (Fintype.card X + ∑ j : Fin m, n j) := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib, spatialDegreeOutput_sum_card hm, Nat.mul_comm]

theorem allocatedSmooth_discrepancy_le_card
    (inactive : LayerSamplerAxis I n → Prop)
    (width : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ)
    (M : ℕ) {W : ℝ} (hW : 0 < W) (hwidth : ∀ i, W ≤ width i) :
    (∑ i, 16 * (probabilityProfileLipschitz : ℝ) * M / width i) ≤
      Fintype.card (AllocatedSmoothRankCoefficientIndex X inactive L) *
        (16 * (probabilityProfileLipschitz : ℝ) * M / W) := by
  calc
    _ ≤ ∑ _i : AllocatedSmoothRankCoefficientIndex X inactive L,
        16 * (probabilityProfileLipschitz : ℝ) * M / W :=
      Finset.sum_le_sum (fun i _ => div_le_div_of_nonneg_left (by positivity) hW (hwidth i))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem allocatedSmooth_discrepancy_le_of_width_budget
    (hm : 0 < m) (inactive : LayerSamplerAxis I n → Prop)
    (width : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ)
    (M D : ℕ) (hD : Fintype.card X + ∑ j : Fin m, n j ≤ D)
    {W η : ℝ} (hW : 0 < W) (hη : 0 < η)
    (hwidth : ∀ i, W ≤ width i)
    (hbudget : 16 * (probabilityProfileLipschitz : ℝ) * M * L * D / η ≤ W) :
    (∑ i, 16 * (probabilityProfileLipschitz : ℝ) * M / width i) ≤ η := by
  have hcount : Fintype.card (AllocatedSmoothRankCoefficientIndex X inactive L) ≤ L * D :=
    (allocatedSmoothRankCoefficientIndex_card_le (X := X) (L := L) hm inactive).trans
      (Nat.mul_le_mul_left L hD)
  have hcountR : (Fintype.card (AllocatedSmoothRankCoefficientIndex X inactive L) : ℝ) ≤
      (L : ℝ) * D := by exact_mod_cast hcount
  have hfrac : 0 ≤ 16 * (probabilityProfileLipschitz : ℝ) * M / W := by positivity
  have hbudget' : 16 * (probabilityProfileLipschitz : ℝ) * M * L * D ≤ η * W := by
    have h := (div_le_iff₀ hη).mp hbudget
    simpa only [mul_comm] using h
  calc
    _ ≤ Fintype.card (AllocatedSmoothRankCoefficientIndex X inactive L) *
        (16 * (probabilityProfileLipschitz : ℝ) * M / W) :=
      allocatedSmooth_discrepancy_le_card inactive width M hW hwidth
    _ ≤ ((L : ℝ) * D) * (16 * (probabilityProfileLipschitz : ℝ) * M / W) :=
      mul_le_mul_of_nonneg_right hcountR hfrac
    _ = (16 * (probabilityProfileLipschitz : ℝ) * M * L * D) / W := by ring
    _ ≤ η := (div_le_iff₀ hW).mpr hbudget'

end Erdos3.VectorPolynomial

end

end OAI
