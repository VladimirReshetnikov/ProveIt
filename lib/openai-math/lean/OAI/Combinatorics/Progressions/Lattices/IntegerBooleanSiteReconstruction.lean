/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.MixedBooleanSiteValues

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem integer_boolean_reconstruction (y : Finset α → ℤ) (s : Finset α) :
    y s = ∑ t : Finset α, if t ⊆ s then booleanCoefficient y t else 0 := by
  have h := congrArg (fun M : Matrix (Finset α) (Finset α) ℤ => M *ᵥ y)
    (booleanReconstruction_mul_extraction (α := α))
  rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at h
  have hv : booleanJetExtractionMatrix (id : Finset α → Finset α) *ᵥ y =
      fun t => booleanCoefficient y t := by
    funext t
    exact booleanJetExtractionMatrix_mulVec id y t
  rw [hv] at h
  have hs := congrFun h s
  simpa only [Matrix.mulVec, dotProduct, booleanReconstructionMatrix,
    ite_mul, one_mul, zero_mul] using hs.symm

theorem integer_boolean_reconstruction_rows (y : Finset α → ℤ)
    (rows : Finset (Finset α)) (hrows : ∀ t ∉ rows, booleanCoefficient y t = 0)
    (s : Finset α) :
    y s = ∑ t ∈ rows, if t ⊆ s then booleanCoefficient y t else 0 := by
  rw [integer_boolean_reconstruction y s]
  symm
  apply Finset.sum_subset (Finset.subset_univ rows)
  intro t _ ht
  simp only [hrows t ht, ite_self]

theorem integer_boolean_sites_bound (y : Finset α → ℤ) (rows : Finset (Finset α))
    (hrows : ∀ t ∉ rows, booleanCoefficient y t = 0)
    {H N : ℝ} (hH : 0 ≤ H) (hN : 0 < N)
    (hcoeff : ∀ t ∈ rows, |((booleanCoefficient y t : ℤ) : ℝ)| ≤ H * N) (s : Finset α) :
    |(y s : ℝ) / N| ≤ rows.card * H := by
  have hs : |(y s : ℝ)| ≤ (rows.card : ℝ) * (H * N) := by
    rw [integer_boolean_reconstruction_rows y rows hrows s, Int.cast_sum]
    calc
      _ ≤ ∑ t ∈ rows, |((if t ⊆ s then booleanCoefficient y t else 0 : ℤ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ rows, H * N := by
        apply Finset.sum_le_sum
        intro t ht
        split_ifs
        · exact hcoeff t ht
        · simp only [Int.cast_zero, abs_zero]
          positivity
      _ = _ := by simp
  rw [abs_div, abs_of_pos hN]
  apply (div_le_iff₀ hN).mpr
  simpa only [mul_assoc] using hs

theorem bounded_affine_site_coefficients_outside_rows {K : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ) (rows : Finset (Finset α))
    (hrows : ∀ t : Finset α, t.card ≤ h → t ∈ rows)
    (c : VectorPolynomial.BoundedCoefficientExponent K h → ℤ) :
    ∀ t ∉ rows, booleanCoefficient
      (VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D) *ᵥ c) t = 0 := by
  intro t ht
  have hh : h < t.card := lt_of_not_ge (fun hle => ht (hrows t hle))
  have heq : VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D) *ᵥ c =
      fun s => ∑ e, c e * VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D) s e := by
    funext s
    apply Finset.sum_congr rfl
    intro e _
    exact mul_comm _ _
  rw [heq, booleanCoefficient_sum]
  apply Finset.sum_eq_zero
  intro e _
  rw [booleanCoefficient_const_mul,
    BooleanCubeKernel.boundedSiteMatrix_high_jet_zero root D h e t hh, mul_zero]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def integerBooleanSitesFromRows (rows : Finset (Finset α))
    (z : rows → ℤ) : Finset α → ℤ :=
  booleanReconstructionMatrix α *ᵥ (fun t => if ht : t ∈ rows then z ⟨t, ht⟩ else 0)

theorem integerBooleanSitesFromRows_coefficient (rows : Finset (Finset α))
    (z : rows → ℤ) (t : Finset α) :
    booleanCoefficient (integerBooleanSitesFromRows rows z) t =
      if ht : t ∈ rows then z ⟨t, ht⟩ else 0 := by
  calc
    _ = (booleanJetExtractionMatrix (id : Finset α → Finset α) *ᵥ
        integerBooleanSitesFromRows rows z) t :=
      (booleanJetExtractionMatrix_mulVec id (integerBooleanSitesFromRows rows z) t).symm
    _ = _ := by
      unfold integerBooleanSitesFromRows
      rw [Matrix.mulVec_mulVec, booleanJetExtraction_mul_reconstruction, Matrix.one_mulVec]

theorem integerBooleanSitesFromRows_coefficient_mem (rows : Finset (Finset α))
    (z : rows → ℤ) (t : rows) :
    booleanCoefficient (integerBooleanSitesFromRows rows z) t.val = z t := by
  rw [integerBooleanSitesFromRows_coefficient, dite_eq_left t.property]

theorem integerBooleanSitesFromRows_coefficient_outside (rows : Finset (Finset α))
    (z : rows → ℤ) (t : Finset α) (ht : t ∉ rows) :
    booleanCoefficient (integerBooleanSitesFromRows rows z) t = 0 := by
  rw [integerBooleanSitesFromRows_coefficient, dite_eq_right ht]

theorem integerBooleanSitesFromRows_eq (rows : Finset (Finset α))
    (y : Finset α → ℤ) (hy : ∀ t ∉ rows, booleanCoefficient y t = 0) :
    integerBooleanSitesFromRows rows (fun t => booleanCoefficient y t.val) = y := by
  have hc : (fun t => if ht : t ∈ rows then
      (fun t : rows => booleanCoefficient y t.val) ⟨t, ht⟩ else 0) =
      fun t => booleanCoefficient y t := by
    funext t
    by_cases ht : t ∈ rows
    · rw [dite_eq_left ht]
    · rw [dite_eq_right ht, hy t ht]
  have he : booleanJetExtractionMatrix (id : Finset α → Finset α) *ᵥ y =
      fun t => booleanCoefficient y t := funext (booleanJetExtractionMatrix_mulVec id y)
  unfold integerBooleanSitesFromRows
  rw [hc, ← he, Matrix.mulVec_mulVec, booleanReconstruction_mul_extraction, Matrix.one_mulVec]

omit [Fintype α] in
theorem integer_boolean_coefficient_bound (y : Finset α → ℤ) (t : Finset α)
    {H N : ℝ} (hy : ∀ s, |(y s : ℝ)| ≤ H * N) :
    |((booleanCoefficient y t : ℤ) : ℝ)| ≤ (2 : ℝ) ^ t.card * (H * N) := by
  rw [booleanCoefficient, Int.cast_sum]
  calc
    _ ≤ ∑ s ∈ t.powerset, |(((-1 : ℤ) ^ (t \ s).card * y s : ℤ) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ t.powerset, H * N := by
      apply Finset.sum_le_sum
      intro s _
      simpa only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, abs_mul,
        abs_pow, abs_neg, abs_one, one_pow, one_mul] using hy s
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset,
      Nat.cast_pow, Nat.cast_ofNat]

omit [Fintype α] in
theorem integer_boolean_coefficient_degree_bound (y : Finset α → ℤ) (t : Finset α)
    {d : ℕ} (ht : t.card ≤ d) {H N : ℝ} (hH : 0 ≤ H) (hN : 0 ≤ N)
    (hy : ∀ s, |(y s : ℝ)| ≤ H * N) :
    |((booleanCoefficient y t : ℤ) : ℝ)| ≤ (2 : ℝ) ^ d * (H * N) :=
  (integer_boolean_coefficient_bound y t hy).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) ht) (mul_nonneg hH hN))

end Erdos3

end

end OAI
