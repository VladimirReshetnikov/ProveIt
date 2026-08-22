import IntegerPoints.ExponentPairs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The Kuz'min–Landau inequality

If `F` is `C¹` on `[A+1, B]` with `F'` monotone and `λ ≤ F' ≤ 1 - λ` there
(`0 < λ ≤ 1/2`), then `‖∑_{A < n ≤ B} e(F(n))‖ ≤ 2/λ`.

The proof is the classical one: with `g_n = F(n+1) - F(n) ∈ [λ, 1-λ]` and
`w(g) = 1/(e(g) - 1) = -1/2 - (i/2) cot(πg)`, one has
`e(F(n)) = (e(F(n+1)) - e(F(n))) w(g_n)`; summation by parts and the
monotonicity of `cot` telescope the resulting sum.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

namespace KL

/-! ### `e` and the weight `w` -/

theorem e_eq (t : ℝ) :
    e t = (Real.cos (2 * π * t) : ℂ) + (Real.sin (2 * π * t) : ℂ) * Complex.I := by
  unfold e
  have : (2 * Real.pi * Complex.I * t : ℂ) = ((2 * π * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

theorem e_add (s t : ℝ) : e (s + t) = e s * e t := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem e_int (m : ℤ) : e m = 1 := by
  unfold e
  have : (2 * Real.pi * Complex.I * ((m : ℝ) : ℂ) : ℂ) = (m : ℂ) * (2 * π * Complex.I) := by
    push_cast
    ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem e_sub_int (t : ℝ) (m : ℤ) : e (t - m) = e t := by
  rw [sub_eq_add_neg, e_add, ← Int.cast_neg, e_int, mul_one]

/-- `cot(π g)`. -/
noncomputable def ct (g : ℝ) : ℝ := Real.cos (π * g) / Real.sin (π * g)

/-- `w(g) = -1/2 - (i/2) cot(π g)`. -/
noncomputable def w (g : ℝ) : ℂ := -1 / 2 - Complex.I / 2 * (ct g : ℂ)

theorem sin_pi_mul_pos {g : ℝ} (h0 : 0 < g) (h1 : g < 1) : 0 < Real.sin (π * g) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])

/-- Multiplication in the form `a + b i`. -/
theorem mul_form (a b c d : ℝ) :
    ((a : ℂ) + (b : ℂ) * Complex.I) * ((c : ℂ) + (d : ℂ) * Complex.I) =
      ((a * c - b * d : ℝ) : ℂ) + ((a * d + b * c : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

/-- `(e(g) - 1) w(g) = 1` for `0 < g < 1`. -/
theorem e_sub_one_mul_w {g : ℝ} (h0 : 0 < g) (h1 : g < 1) : (e g - 1) * w g = 1 := by
  have hs := sin_pi_mul_pos h0 h1
  have hs' : Real.sin (π * g) ≠ 0 := hs.ne'
  have hpy := Real.cos_sq_add_sin_sq (π * g)
  have he : e g - 1 = ((Real.cos (2 * (π * g)) - 1 : ℝ) : ℂ) +
      ((Real.sin (2 * (π * g)) : ℝ) : ℂ) * Complex.I := by
    rw [e_eq, show 2 * π * g = 2 * (π * g) by ring]
    push_cast
    ring
  have hw : w g = ((-1 / 2 : ℝ) : ℂ) + ((-(ct g) / 2 : ℝ) : ℂ) * Complex.I := by
    rw [w]
    push_cast
    ring
  rw [he, hw, mul_form, Real.cos_two_mul, Real.sin_two_mul, ct]
  have hX : (2 * Real.cos (π * g) ^ 2 - 1 - 1) * (-1 / 2) -
      2 * Real.sin (π * g) * Real.cos (π * g) *
        (-(Real.cos (π * g) / Real.sin (π * g)) / 2) = 1 := by
    field_simp
    first
      | ring1
      | linear_combination hpy
      | linear_combination (-1 : ℝ) * hpy
      | linear_combination (2 : ℝ) * hpy
      | linear_combination (-2 : ℝ) * hpy
  have hY : (2 * Real.cos (π * g) ^ 2 - 1 - 1) * (-(Real.cos (π * g) / Real.sin (π * g)) / 2) +
      2 * Real.sin (π * g) * Real.cos (π * g) * (-1 / 2) = 0 := by
    field_simp
    first
      | ring1
      | linear_combination (-(Real.cos (π * g))) * hpy
      | linear_combination (Real.cos (π * g)) * hpy
      | linear_combination (-2 * Real.cos (π * g)) * hpy
      | linear_combination (2 * Real.cos (π * g)) * hpy
  rw [hX, hY]
  simp

/-- `sin(π g) ≥ 2 λ` for `λ ≤ g ≤ 1 - λ`, `λ ≤ 1/2`. -/
theorem two_mul_le_sin_pi_mul {lam g : ℝ} (hl : 0 < lam) (hl' : lam ≤ 1 / 2)
    (hg1 : lam ≤ g) (hg2 : g ≤ 1 - lam) : 2 * lam ≤ Real.sin (π * g) := by
  have key : ∀ u : ℝ, lam ≤ u → u ≤ 1 / 2 → 2 * lam ≤ Real.sin (π * u) := by
    intro u hu1 hu2
    have h1 : 2 * lam ≤ Real.sin (π * lam) := by
      have := Real.mul_le_sin (x := π * lam) (by positivity) (by nlinarith [Real.pi_pos])
      calc 2 * lam = 2 / π * (π * lam) := by field_simp
        _ ≤ Real.sin (π * lam) := this
    have h2 : Real.sin (π * lam) ≤ Real.sin (π * u) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    linarith
  rcases le_or_gt g (1 / 2) with h | h
  · exact key g hg1 h
  · have : Real.sin (π * g) = Real.sin (π * (1 - g)) := by
      rw [← Real.sin_pi_sub]
      congr 1
      ring
    rw [this]
    exact key (1 - g) (by linarith) (by linarith)

theorem abs_ct_le {lam g : ℝ} (hl : 0 < lam) (hl' : lam ≤ 1 / 2)
    (hg1 : lam ≤ g) (hg2 : g ≤ 1 - lam) : |ct g| ≤ 1 / (2 * lam) := by
  have hs := two_mul_le_sin_pi_mul hl hl' hg1 hg2
  have hs0 : 0 < Real.sin (π * g) := by linarith
  rw [ct, abs_div, abs_of_pos hs0, div_le_div_iff₀ hs0 (by positivity)]
  calc |Real.cos (π * g)| * (2 * lam) ≤ 1 * Real.sin (π * g) := by
        apply mul_le_mul (Real.abs_cos_le_one _) hs (by positivity) zero_le_one
    _ = 1 * Real.sin (π * g) := rfl

theorem norm_w_le {lam g : ℝ} (hl : 0 < lam) (hl' : lam ≤ 1 / 2)
    (hg1 : lam ≤ g) (hg2 : g ≤ 1 - lam) : ‖w g‖ ≤ 1 / lam := by
  have hc := abs_ct_le hl hl' hg1 hg2
  have h1 : (1 : ℝ) / 2 ≤ 1 / (2 * lam) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  calc ‖w g‖ ≤ ‖(-1 / 2 : ℂ)‖ + ‖Complex.I / 2 * (ct g : ℂ)‖ := norm_sub_le _ _
    _ = 1 / 2 + 1 / 2 * |ct g| := by
        simp [norm_div, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 1 / (2 * lam) + 1 / 2 * (1 / (2 * lam)) :=
        add_le_add h1 (mul_le_mul_of_nonneg_left hc (by norm_num))
    _ ≤ 1 / lam := by
        have h3 : 1 / (2 * lam) + 1 / 2 * (1 / (2 * lam)) = 3 / 4 * (1 / lam) := by
          field_simp
          ring
        have h4 : 0 < 1 / lam := by positivity
        rw [h3]
        linarith

/-- `cot(π ·)` is antitone on `(0, 1)`. -/
theorem ct_antitone {g₁ g₂ : ℝ} (h0 : 0 < g₁) (h12 : g₁ ≤ g₂) (h1 : g₂ < 1) : ct g₂ ≤ ct g₁ := by
  have hs1 := sin_pi_mul_pos h0 (lt_of_le_of_lt h12 h1)
  have hs2 := sin_pi_mul_pos (lt_of_lt_of_le h0 h12) h1
  rw [ct, ct, div_le_div_iff₀ hs2 hs1]
  have : Real.cos (π * g₁) * Real.sin (π * g₂) - Real.cos (π * g₂) * Real.sin (π * g₁) =
      Real.sin (π * g₂ - π * g₁) := by
    rw [Real.sin_sub]
    ring
  have hnn : 0 ≤ Real.sin (π * g₂ - π * g₁) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  linarith

/-- `w g₁ - w g₂` for the telescoping step. -/
theorem norm_w_sub {g₁ g₂ : ℝ} (h0 : 0 < g₁) (h12 : g₁ ≤ g₂) (h1 : g₂ < 1) :
    ‖w g₂ - w g₁‖ = 1 / 2 * (ct g₁ - ct g₂) := by
  have hct := ct_antitone h0 h12 h1
  have : w g₂ - w g₁ = Complex.I / 2 * ((ct g₁ - ct g₂ : ℝ) : ℂ) := by
    rw [w, w]
    push_cast
    ring
  rw [this, norm_mul, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  norm_num

/-! ### Summation by parts -/

/-- Abel summation in the form used below. -/
theorem abel (a w : ℕ → ℂ) (K : ℕ) :
    ∑ i ∈ range (K + 1), (a (i + 1) - a i) * w i =
      a (K + 1) * w K - a 0 * w 0 - ∑ i ∈ range K, a (i + 1) * (w (i + 1) - w i) := by
  induction K with
  | zero => simp; ring
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

theorem sum_Ioc_eq_sum_range (f : ℕ → ℂ) (A B : ℕ) :
    ∑ n ∈ Finset.Ioc A B, f n = ∑ i ∈ Finset.range (B - A), f (A + 1 + i) := by
  have : Finset.Ioc A B = Finset.Ico (A + 1) (B + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [this, Finset.sum_Ico_eq_sum_range]
  have : B + 1 - (A + 1) = B - A := by omega
  rw [this]

/-- **Kuz'min–Landau**, core form: `F` is `C¹`, `F'` is monotone on
`[A+1, B]` and `λ ≤ F' ≤ 1 - λ` there; then `‖∑_{A < n ≤ B} e(F(n))‖ ≤ 4/λ`. -/
theorem core (F : ℝ → ℝ) (A B : ℕ) (lam : ℝ) (hl : 0 < lam) (hl' : lam ≤ 1 / 2)
    (hF : ContDiff ℝ 1 F)
    (hmono : MonotoneOn (deriv F) (Set.Icc (A + 1 : ℝ) B))
    (hrange : ∀ t ∈ Set.Icc (A + 1 : ℝ) B, lam ≤ deriv F t ∧ deriv F t ≤ 1 - lam) :
    ‖∑ n ∈ Finset.Ioc A B, e (F n)‖ ≤ 4 / lam := by
  have h1l : (1 : ℝ) ≤ 1 / lam := by
    rw [le_div_iff₀ hl]
    linarith
  have h4l : 0 < 4 / lam := by positivity
  have h14 : 1 / lam ≤ 4 / lam := div_le_div_of_nonneg_right (by norm_num) hl.le
  rw [sum_Ioc_eq_sum_range]
  set L := B - A with hL
  set a : ℕ → ℂ := fun i => e (F ((A + 1 + i : ℕ) : ℝ)) with ha
  set g : ℕ → ℝ := fun i => F ((A + 2 + i : ℕ) : ℝ) - F ((A + 1 + i : ℕ) : ℝ) with hg
  have hcont : Continuous F := hF.continuous
  have hdiff : Differentiable ℝ F := hF.differentiable one_ne_zero
  -- mean value theorem for the differences
  have hmvt : ∀ i, i + 1 < L →
      ∃ c : ℝ, ((A + 1 + i : ℕ) : ℝ) < c ∧ c < ((A + 2 + i : ℕ) : ℝ) ∧ g i = deriv F c := by
    intro i _
    have hlt : ((A + 1 + i : ℕ) : ℝ) < ((A + 2 + i : ℕ) : ℝ) := by
      push_cast
      linarith
    obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope F hlt hcont.continuousOn hdiff.differentiableOn
    refine ⟨c, hc.1, hc.2, ?_⟩
    rw [hc', show ((A + 2 + i : ℕ) : ℝ) - ((A + 1 + i : ℕ) : ℝ) = 1 by push_cast; ring, div_one]
  have hcIcc : ∀ i, i + 1 < L → ∀ c : ℝ, ((A + 1 + i : ℕ) : ℝ) < c → c < ((A + 2 + i : ℕ) : ℝ) →
      c ∈ Set.Icc (A + 1 : ℝ) B := by
    intro i hi c hc1 hc2
    have h1 : (A + 1 : ℝ) ≤ ((A + 1 + i : ℕ) : ℝ) := by push_cast; linarith
    have h2 : ((A + 2 + i : ℕ) : ℝ) ≤ B := by
      have : A + 2 + i ≤ B := by omega
      exact_mod_cast this
    exact ⟨by linarith, by linarith⟩
  have hgrange : ∀ i, i + 1 < L → lam ≤ g i ∧ g i ≤ 1 - lam := by
    intro i hi
    obtain ⟨c, hc1, hc2, hgc⟩ := hmvt i hi
    rw [hgc]
    exact hrange c (hcIcc i hi c hc1 hc2)
  have hgmono : ∀ i, i + 2 < L → g i ≤ g (i + 1) := by
    intro i hi
    obtain ⟨c, hc1, hc2, hgc⟩ := hmvt i (by omega)
    obtain ⟨c', hc1', hc2', hgc'⟩ := hmvt (i + 1) (by omega)
    rw [hgc, hgc']
    have hcc : c ≤ c' := by
      have : ((A + 2 + i : ℕ) : ℝ) = ((A + 1 + (i + 1) : ℕ) : ℝ) := by push_cast; ring
      linarith
    exact hmono (hcIcc i (by omega) c hc1 hc2) (hcIcc (i + 1) (by omega) c' hc1' hc2') hcc
  -- the basic identity `a_i = (a_{i+1} - a_i) w(g_i)`
  have hrec : ∀ i, i + 1 < L → a i = (a (i + 1) - a i) * w (g i) := by
    intro i hi
    have hgi := hgrange i hi
    have hnext : a (i + 1) = a i * e (g i) := by
      rw [ha]
      simp only
      rw [← e_add]
      congr 1
      rw [hg]
      simp only
      rw [show A + 1 + (i + 1) = A + 2 + i by omega]
      ring
    rw [hnext, ← mul_sub_one, mul_assoc, e_sub_one_mul_w (by linarith) (by linarith), mul_one]
  -- bounds
  have hnorm_a : ∀ i, ‖a i‖ = 1 := fun i => norm_e _
  -- case analysis on the length
  rcases Nat.lt_or_ge L 2 with hL2 | hL2
  · interval_cases L
    · simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
      exact h4l.le
    · simp only [Finset.range_one, Finset.sum_singleton, hnorm_a]
      linarith
  obtain ⟨K, hK⟩ : ∃ K, L = K + 2 := ⟨L - 2, by omega⟩
  rw [hK, Finset.sum_range_succ, Finset.sum_congr rfl (fun i hi => hrec i (by
    rw [Finset.mem_range] at hi; omega)), abel]
  have hw0 := norm_w_le hl hl' (hgrange 0 (by omega)).1 (hgrange 0 (by omega)).2
  have hwK := norm_w_le hl hl' (hgrange K (by omega)).1 (hgrange K (by omega)).2
  have htel : ‖∑ i ∈ range K, a (i + 1) * (w (g (i + 1)) - w (g i))‖ ≤ 1 / (2 * lam) := by
    calc ‖∑ i ∈ range K, a (i + 1) * (w (g (i + 1)) - w (g i))‖
        ≤ ∑ i ∈ range K, ‖a (i + 1) * (w (g (i + 1)) - w (g i))‖ := norm_sum_le _ _
      _ = ∑ i ∈ range K, 1 / 2 * (ct (g i) - ct (g (i + 1))) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_range] at hi
          rw [norm_mul, hnorm_a, one_mul]
          have h0 := hgrange i (by omega)
          have h1 := hgrange (i + 1) (by omega)
          exact norm_w_sub (by linarith) (hgmono i (by omega)) (by linarith)
      _ = 1 / 2 * (ct (g 0) - ct (g K)) := by
          rw [← Finset.mul_sum, Finset.sum_range_sub' (fun i => ct (g i))]
      _ ≤ 1 / 2 * (1 / (2 * lam) + 1 / (2 * lam)) := by
          have h0 := abs_ct_le hl hl' (hgrange 0 (by omega)).1 (hgrange 0 (by omega)).2
          have hK' := abs_ct_le hl hl' (hgrange K (by omega)).1 (hgrange K (by omega)).2
          have := le_abs_self (ct (g 0))
          have := neg_abs_le (ct (g K))
          nlinarith
      _ = 1 / (2 * lam) := by ring
  have h12 : 1 / (2 * lam) ≤ 1 / lam := by
    rw [div_le_div_iff₀ (by positivity) hl]
    linarith
  calc ‖a (K + 1) * w (g K) - a 0 * w (g 0) -
          ∑ i ∈ range K, a (i + 1) * (w (g (i + 1)) - w (g i)) + a (K + 1)‖
      ≤ ‖a (K + 1) * w (g K) - a 0 * w (g 0) -
          ∑ i ∈ range K, a (i + 1) * (w (g (i + 1)) - w (g i))‖ + ‖a (K + 1)‖ := norm_add_le _ _
    _ ≤ ‖a (K + 1) * w (g K) - a 0 * w (g 0)‖ +
          ‖∑ i ∈ range K, a (i + 1) * (w (g (i + 1)) - w (g i))‖ + ‖a (K + 1)‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ (‖a (K + 1) * w (g K)‖ + ‖a 0 * w (g 0)‖) +
          ‖∑ i ∈ range K, a (i + 1) * (w (g (i + 1)) - w (g i))‖ + ‖a (K + 1)‖ := by
        gcongr
        exact norm_sub_le _ _
    _ = (‖w (g K)‖ + ‖w (g 0)‖) +
          ‖∑ i ∈ range K, a (i + 1) * (w (g (i + 1)) - w (g i))‖ + 1 := by
        simp only [norm_mul, hnorm_a, one_mul]
    _ ≤ (1 / lam + 1 / lam) + 1 / (2 * lam) + 1 := by gcongr
    _ ≤ 4 / lam := by
        have : 4 / lam = 1 / lam + 1 / lam + 1 / lam + 1 / lam := by ring
        linarith


/-! ### The general form -/

theorem nearestIntDist_sub_int (x : ℝ) (m : ℤ) : nearestIntDist (x - m) = nearestIntDist x := by
  unfold nearestIntDist
  rw [round_sub_intCast]
  push_cast
  congr 1
  ring

theorem nearestIntDist_le (x : ℝ) (m : ℤ) : nearestIntDist x ≤ |x - m| := round_le x m

theorem nearestIntDist_intCast (m : ℤ) : nearestIntDist m = 0 := by
  unfold nearestIntDist
  rw [round_intCast, sub_self, abs_zero]

theorem nearestIntDist_neg (x : ℝ) : nearestIntDist (-x) = nearestIntDist x := by
  apply le_antisymm
  · calc nearestIntDist (-x) ≤ |-x - ((-round x : ℤ) : ℝ)| := nearestIntDist_le _ _
      _ = nearestIntDist x := by
          unfold nearestIntDist
          push_cast
          rw [← abs_neg]
          congr 1
          ring
  · calc nearestIntDist x ≤ |x - ((-round (-x) : ℤ) : ℝ)| := nearestIntDist_le _ _
      _ = nearestIntDist (-x) := by
          unfold nearestIntDist
          push_cast
          rw [← abs_neg]
          congr 1
          ring

theorem e_neg (t : ℝ) : e (-t) = starRingEnd ℂ (e t) := by
  rw [e_eq, e_eq, mul_neg, Real.cos_neg, Real.sin_neg, map_add, map_mul, Complex.conj_ofReal,
    Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem deriv_neg_fun (G : ℝ → ℝ) : deriv (fun t => -G t) = fun t => -deriv G t := by
  ext t
  exact deriv.neg

/-- **Kuz'min–Landau.** If `F` is `C¹`, `F'` is monotone or antitone on
`[A+1, B]`, and `‖F'(t)‖ ≥ λ` there (`0 < λ ≤ 1/2`), then
`‖∑_{A < n ≤ B} e(F(n))‖ ≤ 4/λ`. -/
theorem kuzmin_landau (F : ℝ → ℝ) (A B : ℕ) (lam : ℝ) (hl : 0 < lam) (hl' : lam ≤ 1 / 2)
    (hF : ContDiff ℝ 1 F)
    (hmono : MonotoneOn (deriv F) (Set.Icc (A + 1 : ℝ) B) ∨
      AntitoneOn (deriv F) (Set.Icc (A + 1 : ℝ) B))
    (hdist : ∀ t ∈ Set.Icc (A + 1 : ℝ) B, lam ≤ nearestIntDist (deriv F t)) :
    ‖∑ n ∈ Finset.Ioc A B, e (F n)‖ ≤ 4 / lam := by
  -- reduce to the monotone case
  suffices key : ∀ G : ℝ → ℝ, ContDiff ℝ 1 G → MonotoneOn (deriv G) (Set.Icc (A + 1 : ℝ) B) →
      (∀ t ∈ Set.Icc (A + 1 : ℝ) B, lam ≤ nearestIntDist (deriv G t)) →
      ‖∑ n ∈ Finset.Ioc A B, e (G n)‖ ≤ 4 / lam by
    rcases hmono with h | h
    · exact key F hF h hdist
    · have hsum : ∑ n ∈ Finset.Ioc A B, e ((fun t => -F t) n) =
          starRingEnd ℂ (∑ n ∈ Finset.Ioc A B, e (F n)) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun n _ => e_neg _
      have := key (fun t => -F t) hF.neg (by rw [deriv_neg_fun]; exact h.neg)
        (fun t ht => by rw [deriv_neg_fun]; simp only; rw [nearestIntDist_neg]; exact hdist t ht)
      rwa [hsum, Complex.norm_conj] at this
  intro G hG hmono hdist
  rcases Nat.lt_or_ge B (A + 1) with hBA | hBA
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    positivity
  have hAB' : (A + 1 : ℝ) ≤ B := by exact_mod_cast hBA
  have ht₀ : (A + 1 : ℝ) ∈ Set.Icc (A + 1 : ℝ) B := ⟨le_rfl, hAB'⟩
  have hcontd : Continuous (deriv G) := hG.continuous_deriv le_rfl
  -- the integer shift
  set u₀ := deriv G (A + 1) with hu₀
  set k : ℤ := if 0 ≤ u₀ - round u₀ then round u₀ else round u₀ - 1 with hk
  have hk0 : lam ≤ u₀ - k ∧ u₀ - k ≤ 1 - lam := by
    have h1 := hdist _ ht₀
    have h2 := abs_le.1 (abs_sub_round u₀)
    unfold nearestIntDist at h1
    rw [hk]
    split_ifs with h
    · rw [abs_of_nonneg h] at h1
      exact ⟨h1, by linarith⟩
    · push Not at h
      rw [abs_of_neg h] at h1
      push_cast
      exact ⟨by linarith, by linarith⟩
  -- the shifted derivative stays in `[λ, 1 - λ]`
  have hshift : ∀ t ∈ Set.Icc (A + 1 : ℝ) B, lam ≤ deriv G t - k ∧ deriv G t - k ≤ 1 - lam := by
    intro t ht
    have hd := hdist t ht
    have hcu : ContinuousOn (fun s => deriv G s - k) (Set.uIcc (A + 1 : ℝ) t) :=
      (hcontd.sub continuous_const).continuousOn
    have hsub : Set.uIcc (A + 1 : ℝ) t ⊆ Set.Icc (A + 1 : ℝ) B := by
      rw [Set.uIcc_of_le ht.1]
      exact Set.Icc_subset_Icc le_rfl ht.2
    constructor
    · by_contra hlt
      push Not at hlt
      have hle : deriv G t - k ≤ -lam := by
        have h1 := le_trans hd (nearestIntDist_le (deriv G t) k)
        rcases le_abs.1 h1 with h | h
        · linarith
        · linarith
      obtain ⟨s, hs, hs0⟩ := intermediate_value_uIcc hcu
        (show (0 : ℝ) ∈ Set.uIcc (deriv G (A + 1) - k) (deriv G t - k) from
          Set.mem_uIcc.2 (Or.inr ⟨by linarith, by linarith [hk0.1]⟩))
      have := hdist s (hsub hs)
      rw [← nearestIntDist_sub_int (deriv G s) k] at this
      simp only at hs0
      rw [hs0, ← Int.cast_zero, nearestIntDist_intCast] at this
      linarith
    · by_contra hgt
      push Not at hgt
      have hge : 1 + lam ≤ deriv G t - k := by
        have h1 := le_trans hd (nearestIntDist_le (deriv G t) (k + 1))
        push_cast at h1
        rcases le_abs.1 h1 with h | h
        · linarith
        · linarith
      obtain ⟨s, hs, hs0⟩ := intermediate_value_uIcc hcu
        (show (1 : ℝ) ∈ Set.uIcc (deriv G (A + 1) - k) (deriv G t - k) from
          Set.mem_uIcc.2 (Or.inl ⟨by linarith [hk0.2], by linarith⟩))
      have := hdist s (hsub hs)
      rw [← nearestIntDist_sub_int (deriv G s) k] at this
      simp only at hs0
      rw [hs0, ← Int.cast_one, nearestIntDist_intCast] at this
      linarith
  -- apply the core inequality to `G - k t`
  have hdiffG : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hG' : deriv (fun t => G t - k * t) = fun t => deriv G t - k := by
    ext t
    have h := ((hdiffG t).hasDerivAt.sub ((hasDerivAt_id t).const_mul (k : ℝ))).deriv
    simp only [id_eq, mul_one] at h
    exact h
  have hcore := core (fun t => G t - k * t) A B lam hl hl'
    (hG.sub (contDiff_const.mul contDiff_id))
    (by
      rw [hG']
      intro a ha b hb hab
      exact sub_le_sub_right (hmono ha hb hab) _)
    (by rw [hG']; exact hshift)
  have hsum : ∑ n ∈ Finset.Ioc A B, e ((fun t => G t - k * t) n) =
      ∑ n ∈ Finset.Ioc A B, e (G n) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only
    rw [show (k : ℝ) * (n : ℝ) = ((k * n : ℤ) : ℝ) by push_cast; ring, e_sub_int]
  rwa [hsum] at hcore


end KL

end LeanProofs.IntegerPoints
