import OAI.Combinatorics.Progressions.Estimates.CorrelationDerivative
import OAI.Combinatorics.Progressions.Estimates.FixedPartnerPower
import OAI.Combinatorics.Progressions.Linear.BalancedDualBounds

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {H Ω : Type*} [Fintype H] [Fintype Ω]

theorem square_norm_mean_eq_cross_re (v : H → ℂ) :
    ‖𝔼 h, v h‖ ^ 2 = (𝔼 h, 𝔼 k, v h * star (v k)).re := by
  rw [← Fintype.expect_mul_expect, expect_star, mul_star_re_eq_norm_sq]

theorem mean_square_family_le_cross_norm (v : H → Ω → ℂ) :
    (𝔼 x, ‖𝔼 h, v h x‖ ^ 2) ≤ 𝔼 h, 𝔼 k, ‖𝔼 x, v h x * star (v k x)‖ := by
  simp_rw [square_norm_mean_eq_cross_re]
  rw [← expect_re, Finset.expect_comm]
  have hid (h : H) :
      (𝔼 x, 𝔼 k, v h x * star (v k x)) = 𝔼 k, 𝔼 x, v h x * star (v k x) :=
    Finset.expect_comm _ _ _
  simp_rw [hid, expect_re]
  apply Finset.expect_le_expect
  intro h _
  apply Finset.expect_le_expect
  intro k _
  rw [← expect_re]
  exact Complex.re_le_norm _

theorem finite_family_cauchy_schwarz [Nonempty Ω]
    (B : Ω → ℂ) (v : H → Ω → ℂ) {M : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) :
    ‖𝔼 x, B x * (𝔼 h, v h x)‖ ^ 2 ≤
      M ^ 2 * (𝔼 h, 𝔼 k, ‖𝔼 x, v h x * star (v k x)‖) := by
  have hcs := norm_expect_mul_star_sq_le B (fun x => star (𝔼 h, v h x))
  simp only [star_star, norm_star] at hcs
  have hBM : (𝔼 x, ‖B x‖ ^ 2) ≤ M ^ 2 :=
    (Finset.expect_le_expect (fun x _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hB x) 2)).trans_eq (Fintype.expect_const _)
  exact hcs.trans ((mul_le_mul_of_nonneg_right hBM
    (Finset.expect_nonneg (fun x _ => sq_nonneg _))).trans
      (mul_le_mul_of_nonneg_left (mean_square_family_le_cross_norm v) (sq_nonneg M)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem shift_phase_average (v B : G → ℂ) (L : G → G → ℂ) (a : G → ℂ)
    (ha : ∀ h, a h * (𝔼 x, v x * (B (x + h) * L h x)) =
      (‖𝔼 x, v x * (B (x + h) * L h x)‖ : ℂ)) :
    (𝔼 y, B y * (𝔼 h, a h * v (y - h) * L h (y - h))) =
      ((𝔼 h, ‖𝔼 x, v x * (B (x + h) * L h x)‖) : ℝ) := by
  have hmove (h : G) :
      a h * (𝔼 x, v x * (B (x + h) * L h x)) =
        𝔼 y, B y * (a h * v (y - h) * L h (y - h)) := by
    rw [Finset.mul_expect]
    apply Fintype.expect_equiv (Equiv.addRight h)
    intro x
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    ring
  calc
    _ = 𝔼 h, 𝔼 y, B y * (a h * v (y - h) * L h (y - h)) := by
      simp_rw [Finset.mul_expect]
      rw [Finset.expect_comm]
    _ = 𝔼 h, a h * (𝔼 x, v x * (B (x + h) * L h x)) := by simp_rw [← hmove]
    _ = _ := by simp_rw [ha]; simp [Fintype.expect_eq_sum_div_card]

theorem shift_phase_cross_norm (v : G → ℂ) (L : G → G → ℂ) (a : G → ℂ)
    (ha : ∀ h, ‖a h‖ = 1) (h k : G) :
    ‖𝔼 y, (a h * v (y - h) * L h (y - h)) *
      star (a k * v (y - k) * L k (y - k))‖ =
    ‖𝔼 x, v x * star (v (x + h - k)) * L h x * star (L k (x + h - k))‖ := by
  have hid : (a h * star (a k)) *
      (𝔼 x, v x * star (v (x + h - k)) * L h x * star (L k (x + h - k))) =
      𝔼 y, (a h * v (y - h) * L h (y - h)) *
        star (a k * v (y - k) * L k (y - k)) := by
    rw [Finset.mul_expect]
    apply Fintype.expect_equiv (Equiv.addRight h)
    intro x
    simp only [Equiv.coe_addRight, add_sub_cancel_right, star_mul]
    ring
  rw [← hid, norm_mul, norm_mul, norm_star, ha, ha, one_mul, one_mul]

theorem shifted_test_cauchy_schwarz (v B : G → ℂ) (L : G → G → ℂ)
    {M : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) :
    (𝔼 h, ‖𝔼 x, v x * (B (x + h) * L h x)‖) ^ 2 ≤
      M ^ 2 * (𝔼 h, 𝔼 k,
        ‖𝔼 x, v x * star (v (x + h - k)) * L h x * star (L k (x + h - k))‖) := by
  have hex (h : G) := exists_complex_unit_phase (𝔼 x, v x * (B (x + h) * L h x))
  choose a ha hphase using hex
  have hcs := finite_family_cauchy_schwarz B
    (fun h y => a h * v (y - h) * L h (y - h)) hB
  rw [shift_phase_average v B L a hphase, Complex.norm_real,
    Real.norm_of_nonneg (Finset.expect_nonneg (fun h _ => norm_nonneg _))] at hcs
  simpa only [shift_phase_cross_norm v L a ha] using hcs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_absolute_cauchy_schwarz {H Ω : Type*} [Fintype H] [Fintype Ω]
    [Nonempty Ω] (B : Ω → ℂ) (v : H → Ω → ℂ) {M : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) :
    (𝔼 h, ‖𝔼 x, B x * v h x‖) ^ 2 ≤
      M ^ 2 * (𝔼 h, 𝔼 k, ‖𝔼 x, v h x * star (v k x)‖) := by
  choose a ha hphase using fun h => exists_complex_unit_phase (𝔼 x, B x * v h x)
  have havg : (𝔼 x, B x * (𝔼 h, a h * v h x)) =
      ((𝔼 h, ‖𝔼 x, B x * v h x‖) : ℝ) := by
    calc
      _ = 𝔼 h, a h * (𝔼 x, B x * v h x) := by
        simp_rw [Finset.mul_expect]
        rw [Finset.expect_comm]
        apply Finset.expect_congr rfl
        intro h _
        apply Finset.expect_congr rfl
        intro x _
        ring
      _ = _ := by simp_rw [hphase]; simp [Fintype.expect_eq_sum_div_card]
  have hcross (h k : H) :
      ‖𝔼 x, (a h * v h x) * star (a k * v k x)‖ =
        ‖𝔼 x, v h x * star (v k x)‖ := by
    have hid : (𝔼 x, (a h * v h x) * star (a k * v k x)) =
        (a h * star (a k)) * (𝔼 x, v h x * star (v k x)) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      simp only [star_mul]
      ring
    rw [hid, norm_mul, norm_mul, norm_star, ha, ha, one_mul, one_mul]
  have hcs := finite_family_cauchy_schwarz B (fun h x => a h * v h x) hB
  rw [havg, Complex.norm_real,
    Real.norm_of_nonneg (Finset.expect_nonneg (fun h _ => norm_nonneg _))] at hcs
  simpa only [hcross] using hcs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G ι : Type*} [AddCommGroup G] [Fintype G] [Nonempty ι]

theorem exists_shift_tests_of_lt_seminorm (v B : G → ℂ) (T : ι → G → ℂ)
    {M a : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1)
    (ha : 0 ≤ a) (hlt : a < shiftTestingSeminorm B T v) :
    ∃ t : G → ι, a ^ 2 ≤ M ^ 2 * (𝔼 h, 𝔼 k,
      ‖𝔼 x, v x * star (v (x + h - k)) * T (t h) x * star (T (t k) (x + h - k))‖) := by
  let eta := (shiftTestingSeminorm B T v - a) / 2
  have heta : 0 < eta := by dsimp only [eta]; linarith
  obtain ⟨t, ht⟩ := exists_nearly_maximizing_shift_tests B T hB hT v heta
  have havg : a ≤ 𝔼 h, ‖𝔼 x, v x * (B (x + h) * T (t h) x)‖ := by
    dsimp only [eta] at ht
    linarith
  exact ⟨t, (pow_le_pow_left₀ ha havg 2).trans
    (shifted_test_cauchy_schwarz v B (fun h => T (t h)) hB)⟩

theorem exists_shift_tests_of_seminorm_large (v B : G → ℂ) (T : ι → G → ℂ)
    {M tau : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1)
    (htau : 0 < tau) (hlarge : tau ≤ shiftTestingSeminorm B T v) :
    ∃ t : G → ι, tau ^ 2 / 4 ≤ M ^ 2 * (𝔼 h, 𝔼 k,
      ‖𝔼 x, v x * star (v (x + h - k)) * T (t h) x * star (T (t k) (x + h - k))‖) := by
  obtain ⟨t, ht⟩ := exists_shift_tests_of_lt_seminorm v B T hB hT
    (a := tau / 2) (by positivity) (by linarith)
  exact ⟨t, (by convert ht using 1; ring)⟩

theorem shiftTestingSeminorm_sq_le_of_cross_bound (v B : G → ℂ) (T : ι → G → ℂ)
    {M D : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1) (hD : 0 ≤ D)
    (hcross : ∀ t : G → ι, (𝔼 h, 𝔼 k,
      ‖𝔼 x, v x * star (v (x + h - k)) * T (t h) x * star (T (t k) (x + h - k))‖) ≤ D) :
    (shiftTestingSeminorm B T v) ^ 2 ≤ M ^ 2 * D := by
  have hroot := Real.sq_sqrt (mul_nonneg (sq_nonneg M) hD)
  have hle : shiftTestingSeminorm B T v ≤ Real.sqrt (M ^ 2 * D) := by
    by_contra h
    have hlt := lt_of_not_ge h
    let a := (shiftTestingSeminorm B T v + Real.sqrt (M ^ 2 * D)) / 2
    have ha : 0 ≤ a := by dsimp only [a]; positivity
    have hasmall : a < shiftTestingSeminorm B T v := by dsimp only [a]; linarith
    obtain ⟨t, ht⟩ := exists_shift_tests_of_lt_seminorm v B T hB hT ha hasmall
    have hu := ht.trans (mul_le_mul_of_nonneg_left (hcross t) (sq_nonneg M))
    have hbig : Real.sqrt (M ^ 2 * D) < a := by dsimp only [a]; linarith
    nlinarith [Real.sqrt_nonneg (M ^ 2 * D)]
  exact (pow_le_pow_left₀ (apply_nonneg _ _) hle 2).trans_eq hroot

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G ι : Type*} [AddCommGroup G] [Fintype G]

theorem shift_derivative_correlation_le_one (v : G → ℂ) (T : ι → G → ℂ)
    (hv : ∀ x, ‖v x‖ ≤ 1) (hT : ∀ i x, ‖T i x‖ ≤ 1) (i j : ι) (h k : G) :
    ‖𝔼 x, v x * star (v (x + h - k)) * T i x * star (T j (x + h - k))‖ ≤ 1 := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le Finset.univ_nonempty
  intro x _
  simp only [norm_mul, norm_star]
  have hpair := (mul_le_of_le_one_left (norm_nonneg _) (hv x)).trans (hv (x + h - k))
  have htriple := (mul_le_of_le_one_left (norm_nonneg _) hpair).trans (hT i x)
  exact (mul_le_of_le_one_left (norm_nonneg _) htriple).trans (hT j _)

theorem shiftTestingSeminorm_gowers_lower [Nonempty ι] (s : ℕ)
    (v B : G → ℂ) (T : ι → G → ℂ) {M tau delta gamma : ℝ}
    (hM : 0 < M) (htau : 0 < tau) (hdelta : 0 ≤ delta) (hgamma : 0 ≤ gamma)
    (hv : ∀ x, ‖v x‖ ≤ 1) (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1)
    (hlarge : tau ≤ shiftTestingSeminorm B T v)
    (hdet : ∀ (i j : ι) (a : G) (f : G → ℂ), (∀ x, ‖f x‖ ≤ 1) →
      delta ≤ ‖𝔼 x, f x * T i x * star (T j (x + a))‖ → gamma ≤ gowersNorm (s + 1) f) :
    gamma ^ (2 ^ (s + 1)) * (tau ^ 2 / (4 * M ^ 2) - delta) ≤
      gowersNorm (s + 2) v ^ (2 ^ (s + 2)) := by
  obtain ⟨t, ht⟩ := exists_shift_tests_of_seminorm_large v B T hB hT htau hlarge
  let C : G → G → ℝ := fun h k =>
    ‖𝔼 x, v x * star (v (x + h - k)) * T (t h) x * star (T (t k) (x + h - k))‖
  have hmean : tau ^ 2 / (4 * M ^ 2) ≤ 𝔼 h, 𝔼 k, C h k := by
    apply (div_le_iff₀ (show 0 < 4 * M ^ 2 by positivity)).mpr
    change tau ^ 2 / 4 ≤ M ^ 2 * (𝔼 h, 𝔼 k, C h k) at ht
    nlinarith only [ht]
  apply gowersNorm_pow_lower_of_pair_detector s v C hdelta hgamma
    (fun h k => shift_derivative_correlation_le_one v T hv hT (t h) (t k) h k) hmean
  intro h k hc
  apply hdet (t h) (t k) (h - k) (multiplicativeDerivative v (h - k))
  · intro x
    simp only [multiplicativeDerivative, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hv x)).trans (hv _)
  · simpa only [C, multiplicativeDerivative, ← add_sub_assoc] using hc

end Erdos3

end

end OAI
