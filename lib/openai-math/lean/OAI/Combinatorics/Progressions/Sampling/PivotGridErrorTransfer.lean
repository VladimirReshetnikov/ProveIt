import OAI.Combinatorics.Progressions.Linear.PivotNormalizedMatrix

namespace OAI

section

namespace Erdos3

open scoped Matrix BigOperators

theorem weighted_finite_sum_error {R : Type*} [Fintype R]
    (a : R → ℝ) {b E c : ℝ} (hc : 0 ≤ c) (ha : ∀ r, |a r - b| ≤ E) :
    |c * ∑ r, a r - (c * Fintype.card R) * b| ≤ (c * Fintype.card R) * E := by
  have he : c * ∑ r, a r - (c * Fintype.card R) * b = c * ∑ r, (a r - b) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [he, abs_mul, abs_of_nonneg hc]
  calc
    c * |∑ r, (a r - b)| ≤ c * ∑ r, |a r - b| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hc
    _ ≤ c * ∑ _r : R, E := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ => ha r) hc
    _ = _ := by simp [mul_assoc]

theorem pivotFiber_error_of_grid_errors {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) (v : I → ℤ)
    (y₀ : J → ℤ) (hy₀ : pivotFreeAdmissible A B v y₀)
    {m : ℤ} (hm : m ≠ 0) (hdiv : A.det ∣ m)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    (hT : ∀ j, 0 < T j) (w : (I → ℤ) × (J → ℤ) → ℝ)
    (hw : Summable (fun p : {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v} => w p.val))
    {F E : ℝ}
    (hgrid : ∀ r : integerLatticeResidue (pivotFreeLattice A B) m,
      |((m.natAbs : ℝ) ^ Fintype.card J / (∏ j, T j)) *
        (∑' z : J → ℤ, w ((pivotFiberGridEquiv A hA B v y₀ hy₀ hm hdiv).symm (r, z)).val) - F| ≤ E) :
    |((∏ i, P i) / ((∏ i, S i) * (∏ j, T j))) *
        (∑' p : {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v}, w p.val) -
        (((pivotFullImage A B).toAddSubgroup.index : ℝ) / |(normalizedIntegerPivot A S P).det|) * F| ≤
      (((pivotFullImage A B).toAddSubgroup.index : ℝ) / |(normalizedIntegerPivot A S P).det|) * E := by
  let := integerLatticeResidueFintype (pivotFreeLattice A B) hm
  let c : ℝ := ((∏ i, P i) / (∏ i, S i)) / (m.natAbs : ℝ) ^ Fintype.card J
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (div_nonneg (Finset.prod_nonneg fun i _ => (hP i).le)
      (Finset.prod_nonneg fun i _ => (hS i).le)) (by positivity)
  have hcount : c * Fintype.card (integerLatticeResidue (pivotFreeLattice A B) m) =
      ((pivotFullImage A B).toAddSubgroup.index : ℝ) / |(normalizedIntegerPivot A S P).det| := by
    have h := pivotGrid_normalization_factor A hA B S P hS hP hm hdiv
    rw [Nat.card_eq_fintype_card] at h
    simpa only [c, div_mul_eq_mul_div] using h
  have hb := weighted_finite_sum_error
    (fun r : integerLatticeResidue (pivotFreeLattice A B) m =>
      ((m.natAbs : ℝ) ^ Fintype.card J / (∏ j, T j)) *
        (∑' z : J → ℤ, w ((pivotFiberGridEquiv A hA B v y₀ hy₀ hm hdiv).symm (r, z)).val)) hc hgrid
  rw [hcount] at hb
  have hm' : (m.natAbs : ℝ) ^ Fintype.card J ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast Int.natAbs_ne_zero.mpr hm)
  have hprodT : (∏ j, T j) ≠ 0 := (Finset.prod_pos fun j _ => hT j).ne'
  have he : c * ((m.natAbs : ℝ) ^ Fintype.card J / (∏ j, T j)) =
      (∏ i, P i) / ((∏ i, S i) * (∏ j, T j)) := by
    dsimp [c]
    field_simp [hm', hprodT]
  rw [← Finset.mul_sum, ← mul_assoc, he,
    ← pivotFiberGrid_tsum_real A hA B v y₀ hy₀ hm hdiv w hw] at hb
  exact hb

end Erdos3

end

end OAI
