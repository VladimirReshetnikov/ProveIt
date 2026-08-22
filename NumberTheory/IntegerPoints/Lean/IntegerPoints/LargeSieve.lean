import IntegerPoints.ExponentialSums
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Wu's Lemma 2.1 (a Fejér-weighted large-sieve inequality)

We prove `wu_lemma21`.  Put `I_n = [x_n, x_n + 1/Q)` and
`φ = ∑_{n ≤ N} z_n 1_{I_n}`.  Then `∫ φ = Q⁻¹ ∑ z_n` and
`∫ |φ|² = ∑_{j,k} ℜ(z_j \bar z_k) (Q⁻¹ - |x_j - x_k|)₊`.  The hypothesis
`max |x_j - x_k| ≤ 1 - 1/Q` says that `φ` is supported on an interval `S` of
length at most `1`, so Cauchy–Schwarz gives `(∫ |φ|)² ≤ |S| ∫ |φ|² ≤ ∫ |φ|²`,
and `‖∑ z_n‖² = Q² ‖∫ φ‖² ≤ Q² ∫ |φ|²`, which is the claim.
-/

open MeasureTheory Finset Set

namespace LeanProofs.IntegerPoints

namespace LargeSieve

variable (N : ℕ) (Q : ℝ) (z : ℕ → ℂ) (x : ℕ → ℝ)

/-- The interval `I_n = [x_n, x_n + 1/Q)`. -/
def In (n : ℕ) : Set ℝ := Set.Ico (x n) (x n + 1 / Q)

/-- The step function `φ = ∑ z_n 1_{I_n}`. -/
noncomputable def φ (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (In Q x n).indicator (fun _ => z n) t

/-- `|φ|²` written as a double sum of indicators. -/
noncomputable def φ2 (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    (In Q x j ∩ In Q x k).indicator (fun _ => (z j * starRingEnd ℂ (z k)).re) t

theorem volume_In_ne_top (n : ℕ) : volume (In Q x n) ≠ ⊤ := by
  rw [In, Real.volume_Ico]
  exact ENNReal.ofReal_ne_top

theorem integrable_indicator_In (n : ℕ) :
    Integrable ((In Q x n).indicator (fun _ => z n)) :=
  (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const (volume_In_ne_top Q x n))

theorem integrable_φ : Integrable (φ N Q z x) := by
  unfold φ
  exact integrable_finsetSum _ fun n _ => integrable_indicator_In Q z x n

theorem integrable_indicator_inter (j k : ℕ) :
    Integrable ((In Q x j ∩ In Q x k).indicator (fun _ => (z j * starRingEnd ℂ (z k)).re)) :=
  (integrable_indicator_iff (measurableSet_Ico.inter measurableSet_Ico)).2
    (integrableOn_const (ne_top_of_le_ne_top (volume_In_ne_top Q x j)
      (measure_mono Set.inter_subset_left)))

theorem integrable_φ2 : Integrable (φ2 N Q z x) := by
  unfold φ2
  exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    integrable_indicator_inter Q z x j k

theorem normSq_φ (t : ℝ) : ‖φ N Q z x t‖ ^ 2 = φ2 N Q z x t := by
  have h : ‖φ N Q z x t‖ ^ 2 = (φ N Q z x t * starRingEnd ℂ (φ N Q z x t)).re := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  rw [h]
  unfold φ φ2
  rw [map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hj : t ∈ In Q x j <;> by_cases hk : t ∈ In Q x k <;>
    simp [Set.indicator_apply, hj, hk]

theorem integral_φ (hQ : 0 < Q) :
    ∫ t, φ N Q z x t = ((1 / Q : ℝ) : ℂ) * ∑ n ∈ Finset.Icc 1 N, z n := by
  unfold φ
  rw [integral_finsetSum _ fun n _ => integrable_indicator_In Q z x n, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [In, integral_indicator_const _ measurableSet_Ico,
    Real.volume_real_Ico_of_le (by linarith [one_div_pos.2 hQ]), add_sub_cancel_left,
    Complex.real_smul]

theorem integral_φ2 :
    ∫ t, φ2 N Q z x t = ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      (z j * starRingEnd ℂ (z k)).re * max 0 (1 / Q - |x j - x k|) := by
  unfold φ2
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    integrable_indicator_inter Q z x j k]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => integrable_indicator_inter Q z x j k]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [In]
  rw [integral_indicator_const _ (measurableSet_Ico.inter measurableSet_Ico),
    Set.Ico_inter_Ico, Real.volume_real_Ico, smul_eq_mul, mul_comm, max_comm]
  congr 2
  rcases le_total (x j) (x k) with h | h
  · rw [sup_eq_right.2 h, inf_eq_left.2 (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    ring
  · rw [sup_eq_left.2 h, inf_eq_right.2 (by linarith), abs_of_nonneg (by linarith)]
    ring

end LargeSieve

open LargeSieve in
/-- **Wu, Lemma 2.1** (`wu_lemma21`). -/
theorem wu_lemma21_holds : wu_lemma21 := by
  intro N Q z x hN hQ hgap
  have hQ0 : 0 < Q := by linarith
  have hQinv : 0 < 1 / Q := one_div_pos.2 hQ0
  have hne : (Finset.Icc 1 N).Nonempty := ⟨1, by simp [hN]⟩
  obtain ⟨j₀, hj₀, hmin⟩ := Finset.exists_min_image (Finset.Icc 1 N) x hne
  obtain ⟨k₀, hk₀, hmax⟩ := Finset.exists_max_image (Finset.Icc 1 N) x hne
  -- the support interval
  set S : Set ℝ := Set.Icc (x j₀) (x k₀ + 1 / Q) with hS
  have hV : volume.real S = x k₀ + 1 / Q - x j₀ := by
    rw [hS, Real.volume_real_Icc_of_le (by linarith [hmin k₀ hk₀])]
  have hV1 : volume.real S ≤ 1 := by
    rw [hV]
    have := hgap k₀ hk₀ j₀ hj₀
    have := le_abs_self (x k₀ - x j₀)
    linarith
  have hV0 : 0 < volume.real S := by
    rw [hV]
    linarith [hmin k₀ hk₀]
  have hsupp : ∀ t, t ∉ S → φ N Q z x t = 0 := by
    intro t ht
    unfold φ
    refine Finset.sum_eq_zero fun n hn => ?_
    apply Set.indicator_of_notMem
    intro htn
    apply ht
    rw [In, Set.mem_Ico] at htn
    rw [hS, Set.mem_Icc]
    exact ⟨le_trans (hmin n hn) htn.1, by linarith [hmax n hn, htn.2]⟩
  -- Cauchy–Schwarz on `S`
  set a : ℝ := ∫ t, ‖φ N Q z x t‖ with ha
  set V : ℝ := volume.real S with hVdef
  have hintS : Integrable (S.indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hintφ : Integrable (fun t => ‖φ N Q z x t‖) := (integrable_φ N Q z x).norm
  have hint2 := integrable_φ2 N Q z x
  have hpt : ∀ t, (a * S.indicator (fun _ => (1 : ℝ)) t - V * ‖φ N Q z x t‖) ^ 2 =
      a ^ 2 * S.indicator (fun _ => (1 : ℝ)) t - 2 * a * V * ‖φ N Q z x t‖ +
        V ^ 2 * φ2 N Q z x t := by
    intro t
    rw [← normSq_φ]
    by_cases ht : t ∈ S
    · rw [Set.indicator_of_mem ht]
      ring
    · rw [Set.indicator_of_notMem ht, hsupp t ht, norm_zero]
      ring
  have hsq : 0 ≤ ∫ t, (a * S.indicator (fun _ => (1 : ℝ)) t - V * ‖φ N Q z x t‖) ^ 2 :=
    integral_nonneg fun t => sq_nonneg _
  have hexp : ∫ t, (a * S.indicator (fun _ => (1 : ℝ)) t - V * ‖φ N Q z x t‖) ^ 2 =
      a ^ 2 * V - 2 * a * V * a + V ^ 2 * ∫ t, φ2 N Q z x t := by
    simp_rw [hpt]
    rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_indicator_const _ measurableSet_Icc, smul_eq_mul, mul_one]
    · exact hintS.const_mul _
    · exact hintφ.const_mul _
    · exact (hintS.const_mul _).sub (hintφ.const_mul _)
    · exact hint2.const_mul _
  have hCS : a ^ 2 ≤ V * ∫ t, φ2 N Q z x t := by
    rw [hexp] at hsq
    have key : V * (V * (∫ t, φ2 N Q z x t) - a ^ 2) =
        a ^ 2 * V - 2 * a * V * a + V ^ 2 * ∫ t, φ2 N Q z x t := by ring
    rw [← key] at hsq
    exact sub_nonneg.1 ((mul_nonneg_iff_of_pos_left hV0).1 hsq)
  have hI2nn : 0 ≤ ∫ t, φ2 N Q z x t := by
    refine integral_nonneg fun t => ?_
    rw [← normSq_φ]
    positivity
  -- `‖∑ z‖ = Q ‖∫ φ‖ ≤ Q a`
  have hsum : ‖∑ n ∈ Finset.Icc 1 N, z n‖ ≤ Q * a := by
    have h1 : (∑ n ∈ Finset.Icc 1 N, z n) = (Q : ℂ) * ∫ t, φ N Q z x t := by
      rw [integral_φ N Q z x hQ0, ← mul_assoc]
      push_cast
      rw [mul_one_div_cancel (by exact_mod_cast hQ0.ne' : (Q : ℂ) ≠ 0), one_mul]
    rw [h1, norm_mul, Complex.norm_real, Real.norm_of_nonneg hQ0.le]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hQ0.le
  have ha0 : 0 ≤ a := integral_nonneg fun t => norm_nonneg _
  -- assemble
  calc ‖∑ n ∈ Finset.Icc 1 N, z n‖ ^ 2 ≤ (Q * a) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hsum 2
    _ = Q ^ 2 * a ^ 2 := by ring
    _ ≤ Q ^ 2 * (V * ∫ t, φ2 N Q z x t) := mul_le_mul_of_nonneg_left hCS (by positivity)
    _ ≤ Q ^ 2 * (1 * ∫ t, φ2 N Q z x t) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hV1 hI2nn) (by positivity)
    _ = Q * ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          (z j * starRingEnd ℂ (z k)).re * (Q * max 0 (1 / Q - |x j - x k|)) := by
        rw [one_mul, integral_φ2, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = Q * (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ (Finset.Icc 1 N).filter (fun k => |x j - x k| ≤ 1 / Q),
          ((1 - Q * |x j - x k| : ℝ) : ℂ) * z j * starRingEnd ℂ (z k)).re := by
        congr 1
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Complex.re_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_max_of_nonneg _ _ hQ0.le, mul_zero, mul_sub, mul_one_div_cancel (ne_of_gt hQ0)]
        split_ifs with h
        · have h' : Q * |x j - x k| ≤ 1 := by
            have := mul_le_mul_of_nonneg_left h hQ0.le
            rwa [mul_one_div_cancel hQ0.ne'] at this
          rw [max_eq_right (by linarith), mul_assoc, Complex.re_ofReal_mul]
          ring
        · push Not at h
          have h' : 1 < Q * |x j - x k| := by
            have := mul_lt_mul_of_pos_left h hQ0
            rwa [mul_one_div_cancel hQ0.ne'] at this
          rw [max_eq_left (by linarith), mul_zero]

end LeanProofs.IntegerPoints
