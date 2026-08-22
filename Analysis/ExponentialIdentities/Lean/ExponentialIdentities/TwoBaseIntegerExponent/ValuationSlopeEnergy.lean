import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Diagonal energy for finite probability distributions

This file isolates a finite-dimensional inequality used when comparing two valuation-slope
profiles.  The diagonal energy uses the zero-safe convention that a coordinate with
`max (u i) (v i) = 0` contributes zero.
-/

namespace LeanProofs.TwoBaseIntegerExponent.ValuationSlopeEnergy

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- A nonnegative real-valued function of total mass one on a finite type. -/
structure IsProbability (u : ι → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ u i
  sum_eq_one : ∑ i, u i = 1

/-- Total variation distance between two functions on a finite type. -/
noncomputable def totalVariation (u v : ι → ℝ) : ℝ :=
  (∑ i, |u i - v i|) / 2

/-- A zero-safe summand for the diagonal energy. -/
noncomputable def energyTerm (x y : ℝ) : ℝ :=
  if max x y = 0 then 0 else (x - y) ^ 2 / max x y

/-- The diagonal energy between two functions on a finite type. -/
noncomputable def diagonalEnergy (u v : ι → ℝ) : ℝ :=
  ∑ i, energyTerm (u i) (v i)

/-- The two-coordinate alternating minor associated with `p` and `q`. -/
def wedge (u v : ι → ℝ) (p q : ι) : ℝ :=
  u p * v q - u q * v p

private lemma max_eq_half_add_abs (x y : ℝ) :
    max x y = (x + y + |x - y|) / 2 := by
  rcases le_total x y with hxy | hyx
  · rw [max_eq_right hxy, abs_of_nonpos (sub_nonpos.mpr hxy)]
    ring
  · rw [max_eq_left hyx, abs_of_nonneg (sub_nonneg.mpr hyx)]
    ring

private lemma abs_sub_le_max {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |x - y| ≤ max x y := by
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy), max_eq_right hxy]
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx), max_eq_left hyx]
    linarith

theorem totalVariation_nonneg (u v : ι → ℝ) : 0 ≤ totalVariation u v := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)

theorem totalVariation_comm (u v : ι → ℝ) :
    totalVariation u v = totalVariation v u := by
  simp only [totalVariation, abs_sub_comm]

theorem energyTerm_nonneg {x y : ℝ} (hx : 0 ≤ x) (_hy : 0 ≤ y) :
    0 ≤ energyTerm x y := by
  by_cases hzero : max x y = 0
  · simp [energyTerm, hzero]
  · rw [energyTerm, if_neg hzero]
    exact div_nonneg (sq_nonneg _) (le_trans hx (le_max_left _ _))

private lemma abs_sub_sq_le_energyTerm_mul_max {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |x - y| ^ 2 ≤ energyTerm x y * max x y := by
  by_cases hzero : max x y = 0
  · have hx0 : x = 0 := by
      apply le_antisymm
      · simpa [hzero] using (le_max_left x y)
      · exact hx
    have hy0 : y = 0 := by
      apply le_antisymm
      · simpa [hzero] using (le_max_right x y)
      · exact hy
    simp [hx0, hy0, energyTerm]
  · rw [energyTerm, if_neg hzero, sq_abs]
    exact (div_mul_cancel₀ _ hzero).symm.le

private lemma energyTerm_le_abs_sub {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    energyTerm x y ≤ |x - y| := by
  by_cases hzero : max x y = 0
  · simp [energyTerm, hzero]
  · have hmax : 0 < max x y :=
      lt_of_le_of_ne (le_trans hx (le_max_left x y)) (Ne.symm hzero)
    rw [energyTerm, if_neg hzero, div_le_iff₀ hmax, ← sq_abs]
    simpa [pow_two] using
      mul_le_mul_of_nonneg_left (abs_sub_le_max hx hy) (abs_nonneg (x - y))

/-- The sum of the coordinatewise maxima is `1 + TV`. -/
theorem sum_max_eq_one_add_totalVariation {u v : ι → ℝ}
    (hu : IsProbability u) (hv : IsProbability v) :
    (∑ i, max (u i) (v i)) = 1 + totalVariation u v := by
  simp_rw [max_eq_half_add_abs]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib,
    hu.sum_eq_one, hv.sum_eq_one]
  unfold totalVariation
  ring

private theorem sum_positive_part_eq_totalVariation {u v : ι → ℝ}
    (hu : IsProbability u) (hv : IsProbability v) :
    (∑ i, max (u i - v i) 0) = totalVariation u v := by
  simp_rw [max_eq_half_add_abs]
  simp only [sub_zero, add_zero]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    hu.sum_eq_one, hv.sum_eq_one]
  unfold totalVariation
  ring

private theorem sub_le_totalVariation_of_le {u v : ι → ℝ}
    (hu : IsProbability u) (hv : IsProbability v) (p : ι)
    (hp : v p ≤ u p) :
    u p - v p ≤ totalVariation u v := by
  classical
  rw [← sum_positive_part_eq_totalVariation hu hv]
  have hone : u p - v p = max (u p - v p) 0 := by
    exact (max_eq_left (sub_nonneg.mpr hp)).symm
  rw [hone]
  exact Finset.single_le_sum (fun i _ ↦ le_max_right (u i - v i) 0) (Finset.mem_univ p)

private theorem pair_mass_le_one {v : ι → ℝ} (hv : IsProbability v)
    {p q : ι} (hpq : p ≠ q) :
    v p + v q ≤ 1 := by
  classical
  have hsubset : {p, q} ⊆ (Finset.univ : Finset ι) := by simp
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun i _ _ ↦ hv.nonneg i)
  simpa [Finset.sum_pair hpq, hv.sum_eq_one] using hsum

/-- Weighted Cauchy gives the sharp lower bound for the zero-safe diagonal energy. -/
theorem four_mul_totalVariation_sq_div_one_add_le_diagonalEnergy
    {u v : ι → ℝ} (hu : IsProbability u) (hv : IsProbability v) :
    4 * totalVariation u v ^ 2 / (1 + totalVariation u v) ≤
      diagonalEnergy u v := by
  have hcauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := Finset.univ)
    (r := fun i ↦ |u i - v i|)
    (f := fun i ↦ energyTerm (u i) (v i))
    (g := fun i ↦ max (u i) (v i))
    (fun i _ ↦ energyTerm_nonneg (hu.nonneg i) (hv.nonneg i))
    (fun i _ ↦ le_trans (hu.nonneg i) (le_max_left _ _))
    (fun i _ ↦ abs_sub_sq_le_energyTerm_mul_max (hu.nonneg i) (hv.nonneg i))
  have habs : (∑ i, |u i - v i|) = 2 * totalVariation u v := by
    unfold totalVariation
    ring
  rw [habs, sum_max_eq_one_add_totalVariation hu hv] at hcauchy
  change (2 * totalVariation u v) ^ 2 ≤
    diagonalEnergy u v * (1 + totalVariation u v) at hcauchy
  have hden : 0 < 1 + totalVariation u v := by
    linarith [totalVariation_nonneg u v]
  apply (div_le_iff₀ hden).2
  nlinarith

/-- The diagonal energy is at most twice the total variation. -/
theorem diagonalEnergy_le_two_mul_totalVariation
    {u v : ι → ℝ} (hu : IsProbability u) (hv : IsProbability v) :
    diagonalEnergy u v ≤ 2 * totalVariation u v := by
  calc
    diagonalEnergy u v = ∑ i, energyTerm (u i) (v i) := rfl
    _ ≤ ∑ i, |u i - v i| :=
      Finset.sum_le_sum fun i _ ↦ energyTerm_le_abs_sub (hu.nonneg i) (hv.nonneg i)
    _ = 2 * totalVariation u v := by
      unfold totalVariation
      ring

/-- Opposite strict signs at two coordinates force a positive alternating minor. -/
theorem wedge_pos_of_opposite_signs {u v : ι → ℝ} (hu : IsProbability u)
    (hv : IsProbability v) {p q : ι} (hp : v p < u p) (hq : u q < v q) :
    0 < wedge u v p q := by
  have hvq : 0 < v q := lt_of_le_of_lt (hu.nonneg q) hq
  have hfirst : 0 < v q * (u p - v p) :=
    mul_pos hvq (sub_pos.mpr hp)
  have hsecond : 0 ≤ v p * (v q - u q) :=
    mul_nonneg (hv.nonneg p) (sub_nonneg.mpr hq.le)
  rw [wedge]
  nlinarith

/-- An opposite-sign two-coordinate wedge is at most the total variation distance. -/
theorem wedge_le_totalVariation_of_opposite_signs
    {u v : ι → ℝ} (hu : IsProbability u) (hv : IsProbability v)
    {p q : ι} (hp : v p < u p) (hq : u q < v q) :
    wedge u v p q ≤ totalVariation u v := by
  have hpq : p ≠ q := by
    intro hpq
    subst q
    linarith
  have hdp : u p - v p ≤ totalVariation u v :=
    sub_le_totalVariation_of_le hu hv p hp.le
  have hdq : v q - u q ≤ totalVariation v u :=
    sub_le_totalVariation_of_le hv hu q hq.le
  rw [totalVariation_comm v u] at hdq
  have hpair : v p + v q ≤ 1 := pair_mass_le_one hv hpq
  have htv : 0 ≤ totalVariation u v := totalVariation_nonneg u v
  calc
    wedge u v p q = v q * (u p - v p) + v p * (v q - u q) := by
      rw [wedge]
      ring
    _ ≤ v q * totalVariation u v + v p * totalVariation u v :=
      add_le_add
        (mul_le_mul_of_nonneg_left hdp (hv.nonneg q))
        (mul_le_mul_of_nonneg_left hdq (hv.nonneg p))
    _ = (v p + v q) * totalVariation u v := by ring
    _ ≤ 1 * totalVariation u v := mul_le_mul_of_nonneg_right hpair htv
    _ = totalVariation u v := one_mul _

private lemma four_mul_sq_div_one_add_mono {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    4 * a ^ 2 / (1 + a) ≤ 4 * b ^ 2 / (1 + b) := by
  have hb : 0 ≤ b := ha.trans hab
  have hfactor : 0 ≤ (b - a) * (a + b + a * b) := by
    exact mul_nonneg (sub_nonneg.mpr hab) (by nlinarith [mul_nonneg ha hb])
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  nlinarith

/-- A positive wedge threshold supplies simultaneous total-variation and energy lower bounds. -/
theorem totalVariation_and_diagonalEnergy_lower_of_wedge
    {u v : ι → ℝ} (hu : IsProbability u) (hv : IsProbability v)
    {p q : ι} (hp : v p < u p) (hq : u q < v q)
    {c : ℝ} (hc : 0 ≤ c) (hcw : c ≤ wedge u v p q) :
    c ≤ totalVariation u v ∧
      4 * c ^ 2 / (1 + c) ≤ diagonalEnergy u v := by
  have hctv : c ≤ totalVariation u v :=
    hcw.trans (wedge_le_totalVariation_of_opposite_signs hu hv hp hq)
  refine ⟨hctv, ?_⟩
  exact (four_mul_sq_div_one_add_mono hc hctv).trans
    (four_mul_totalVariation_sq_div_one_add_le_diagonalEnergy hu hv)

end LeanProofs.TwoBaseIntegerExponent.ValuationSlopeEnergy
