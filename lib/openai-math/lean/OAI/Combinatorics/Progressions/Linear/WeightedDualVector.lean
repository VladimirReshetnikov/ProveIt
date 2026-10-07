import OAI.Combinatorics.Progressions.Linear.BalancedDualBounds
import OAI.Combinatorics.Progressions.Probability.FiniteProbabilityLipschitz

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

noncomputable def uniformDualVector (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (x : Ω) : ℂ :=
  (Fintype.card Ω : ℂ) * star (f (Pi.single x 1))

omit [Nonempty Ω] in
theorem functional_eq_sum_coordinates (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (v : Ω → ℂ) :
    f v = ∑ x, v x * f (Pi.single x 1) := by
  calc
    _ = f (∑ x, Pi.single x (v x)) := by rw [Finset.univ_sum_single]
    _ = ∑ x, f (Pi.single x (v x)) := map_sum f _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      have h : Pi.single x (v x) = v x • Pi.single x (1 : ℂ) := by
        ext y
        by_cases hy : y = x <;> simp [hy]
      rw [h, map_smul, smul_eq_mul]

theorem functional_eq_uniform_inner (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (v : Ω → ℂ) :
    f v = 𝔼 x, v x * star (uniformDualVector f x) := by
  have hcard : (Fintype.card Ω : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Fintype.expect_eq_sum_div_card, functional_eq_sum_coordinates]
  simp only [uniformDualVector, star_mul, star_natCast, star_star]
  have hsum : (∑ x, v x * (f (Pi.single x 1) * (Fintype.card Ω : ℂ))) =
      (Fintype.card Ω : ℂ) * ∑ x, v x * f (Pi.single x 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum]
  field_simp

omit [Nonempty Ω] in
theorem uniformDualVector_norm (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (x : Ω) :
    ‖uniformDualVector f x‖ = (Fintype.card Ω : ℝ) * ‖f (Pi.single x 1)‖ := by
  simp [uniformDualVector]

omit [Nonempty Ω] in
theorem uniform_single_norm_mean (x : Ω) :
    (𝔼 y, ‖(Pi.single x (1 : ℂ) : Ω → ℂ) y‖) = 1 / (Fintype.card Ω : ℝ) := by
  rw [Fintype.expect_eq_sum_div_card]
  have hpoint : (fun y => ‖(Pi.single x (1 : ℂ) : Ω → ℂ) y‖) = Pi.single x (1 : ℝ) := by
    ext y
    by_cases hy : y = x <;> simp [hy]
  rw [hpoint]
  simp

theorem uniformDualVector_self (f : (Ω → ℂ) →ₗ[ℂ] ℂ) :
    f (uniformDualVector f) = ((𝔼 x, ‖uniformDualVector f x‖ ^ 2) : ℝ) := by
  rw [functional_eq_uniform_inner]
  have hpoint (x : Ω) : uniformDualVector f x * star (uniformDualVector f x) =
      ((‖uniformDualVector f x‖ ^ 2 : ℝ) : ℂ) := by
    change uniformDualVector f x * (starRingEnd ℂ) (uniformDualVector f x) = _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [hpoint]
  simp [Fintype.expect_eq_sum_div_card]

theorem uniformDualVector_cap (X : Seminorm ℂ (Ω → ℂ))
    (f : (Ω → ℂ) →ₗ[ℂ] ℂ) {K tau : ℝ} (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * (𝔼 x, ‖v x‖))
    (hdual : ∀ v, tau * ‖f v‖ ≤ X v) :
    ∀ x, ‖uniformDualVector f x‖ ≤ K / tau := by
  intro x
  have hcard : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hbound := (hdual (Pi.single x 1)).trans (hX (Pi.single x 1))
  rw [uniform_single_norm_mean] at hbound
  have hscaled := mul_le_mul_of_nonneg_left hbound hcard.le
  have hcancel : (Fintype.card Ω : ℝ) * (K * (1 / (Fintype.card Ω : ℝ))) = K := by
    field_simp
  rw [hcancel] at hscaled
  apply (le_div_iff₀ htau).mpr
  rw [uniformDualVector_norm]
  nlinarith only [hscaled]

theorem uniformDualVector_detectable (X : Seminorm ℂ (Ω → ℂ))
    (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (b : Ω → ℂ) {M tau : ℝ}
    (hM : 0 < M) (htau : 0 < tau) (hb : ∀ x, ‖b x‖ ≤ M)
    (hfb : 1 < (f b).re) (hdual : ∀ v, tau * ‖f v‖ ≤ X v) :
    tau / M ^ 2 < X (uniformDualVector f) := by
  have hbMean : (𝔼 x, ‖b x‖ ^ 2) ≤ M ^ 2 :=
    (Finset.expect_le_expect (fun x (_ : x ∈ Finset.univ) =>
      pow_le_pow_left₀ (norm_nonneg _) (hb x) 2)).trans_eq
        (Finset.expect_const Finset.univ_nonempty (M ^ 2))
  have hself : ‖f (uniformDualVector f)‖ = 𝔼 x, ‖uniformDualVector f x‖ ^ 2 := by
    rw [uniformDualVector_self, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.expect_nonneg (fun x _ => sq_nonneg _))]
  have hcs := norm_expect_mul_star_sq_le b (uniformDualVector f)
  rw [← functional_eq_uniform_inner, ← hself] at hcs
  have hupper := mul_le_mul_of_nonneg_right hbMean (norm_nonneg (f (uniformDualVector f)))
  have hnorm : 1 < ‖f b‖ := hfb.trans_le (Complex.re_le_norm _)
  have hlarge : 1 < M ^ 2 * ‖f (uniformDualVector f)‖ := by
    nlinarith only [hcs, hupper, hnorm]
  have hscaled := mul_lt_mul_of_pos_left hlarge htau
  have hdom := mul_le_mul_of_nonneg_left (hdual (uniformDualVector f)) (sq_nonneg M)
  apply (div_lt_iff₀ (pow_pos hM 2)).mpr
  nlinarith only [hscaled, hdom]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

noncomputable def weightedDualVector (p : FiniteProbabilityWeights Ω)
    (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (x : Ω) : ℂ :=
  star (f (Pi.single x 1)) / (p.weight x : ℂ)

theorem functional_eq_weighted_inner (p : FiniteProbabilityWeights Ω)
    (f : (Ω → ℂ) →ₗ[ℂ] ℂ)
    (hzero : ∀ x, p.weight x = 0 → f (Pi.single x 1) = 0) (v : Ω → ℂ) :
    f v = p.correlation v (weightedDualVector p f) := by
  rw [functional_eq_sum_coordinates, FiniteProbabilityWeights.correlation]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p.weight x = 0
  · simp [weightedDualVector, hx, hzero x hx]
  · have hxC : (p.weight x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    simp only [weightedDualVector, star_div₀, Complex.star_def,
      Complex.conj_ofReal, Complex.conj_conj]
    field_simp

theorem weightedDualVector_norm (p : FiniteProbabilityWeights Ω)
    (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (x : Ω) :
    ‖weightedDualVector p f x‖ = ‖f (Pi.single x 1)‖ / p.weight x := by
  rw [weightedDualVector, norm_div, norm_star, Complex.norm_real,
    Real.norm_of_nonneg (p.nonneg x)]

theorem modeling_dual_zero_weight (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (f : (Ω → ℂ) →ₗ[ℂ] ℂ) {K tau : ℝ}
    (htau : 0 < tau) (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖))
    (hdual : ∀ v, tau * ‖f v‖ ≤ X v) :
    ∀ x, p.weight x = 0 → f (Pi.single x 1) = 0 := by
  intro x hx
  have h := (hdual (Pi.single x 1)).trans (hX (Pi.single x 1))
  rw [p.mean_single_norm, hx, mul_zero] at h
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (f (Pi.single x 1))]

theorem weightedDualVector_cap (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (f : (Ω → ℂ) →ₗ[ℂ] ℂ) {K tau : ℝ}
    (hK : 0 ≤ K) (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖))
    (hdual : ∀ v, tau * ‖f v‖ ≤ X v) :
    ∀ x, ‖weightedDualVector p f x‖ ≤ K / tau := by
  intro x
  rw [weightedDualVector_norm]
  rcases (p.nonneg x).eq_or_lt with hx | hx
  · rw [← hx, div_zero]
    exact div_nonneg hK htau.le
  · have h := (hdual (Pi.single x 1)).trans (hX (Pi.single x 1))
    rw [p.mean_single_norm] at h
    apply (div_le_iff₀ hx).mpr
    have h' : ‖f (Pi.single x 1)‖ ≤ (K * p.weight x) / tau :=
      (le_div_iff₀ htau).mpr (by nlinarith only [h])
    calc
      _ ≤ (K * p.weight x) / tau := h'
      _ = _ := by ring

theorem weightedDualVector_detectable (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (b : Ω → ℂ) {M tau : ℝ}
    (hM : 0 < M) (htau : 0 < tau) (hb : ∀ x, ‖b x‖ ≤ M)
    (hfb : 1 < (f b).re) (hdual : ∀ v, tau * ‖f v‖ ≤ X v)
    (hzero : ∀ x, p.weight x = 0 → f (Pi.single x 1) = 0) :
    tau / M ^ 2 < X (weightedDualVector p f) := by
  have hbMean : p.mean (fun x => ‖b x‖ ^ 2) ≤ M ^ 2 :=
    (p.mean_mono (fun x => pow_le_pow_left₀ (norm_nonneg _) (hb x) 2)).trans_eq
      (p.mean_const (M ^ 2))
  have hself : ‖f (weightedDualVector p f)‖ =
      p.mean (fun x => ‖weightedDualVector p f x‖ ^ 2) := by
    rw [functional_eq_weighted_inner p f hzero, p.correlation_self,
      Complex.norm_real, Real.norm_of_nonneg (p.mean_nonneg (fun x => sq_nonneg _))]
  have hcs := p.norm_correlation_sq_le b (weightedDualVector p f)
  rw [← functional_eq_weighted_inner p f hzero, ← hself] at hcs
  have hupper := mul_le_mul_of_nonneg_right hbMean
    (norm_nonneg (f (weightedDualVector p f)))
  have hnorm : 1 < ‖f b‖ := hfb.trans_le (Complex.re_le_norm _)
  have hlarge : 1 < M ^ 2 * ‖f (weightedDualVector p f)‖ := by
    nlinarith only [hcs, hupper, hnorm]
  have hscaled := mul_lt_mul_of_pos_left hlarge htau
  have hdom := mul_le_mul_of_nonneg_left (hdual (weightedDualVector p f)) (sq_nonneg M)
  apply (div_lt_iff₀ (pow_pos hM 2)).mpr
  nlinarith only [hscaled, hdom]

end Erdos3

end

end OAI
