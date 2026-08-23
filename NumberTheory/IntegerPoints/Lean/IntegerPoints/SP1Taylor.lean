import IntegerPoints.GKLemma33
import IntegerPoints.PoissonIntegrals

/-!
# Stationary phase, part 1: the Taylor bounds

Setting for Graham–Kolesnik Lemma 3.4 after normalisation: `g ∈ C⁴`, `g(0) = g'(0) = 0`,
`a < 0 < b`, and on `[a, b]`: `g'' ≥ λ₂ > 0`, `|g'''| ≤ λ₃`, `|g''''| ≤ λ₄`.
With `r(x) = g(x) − g''(0)x²/2` we prove the pointwise bounds used in the proof:

* `|r''(x)| ≤ λ₃|x|`, `|r'(x)| ≤ λ₃x²/2`, `|r(x)| ≤ λ₃|x|³/6`;
* `|x r''(x) − 2 r'(x)| ≤ λ₄|x|³/6` and `|x r'(x) − 3 r(x)| ≤ λ₄x⁴/24`
  (so `(r'/x²)' ≪ λ₄` and `(r/x³)' ≪ λ₄`);
* `|x r''(x) − r'(x)| ≤ 3λ₃x²/2` (so `(g'/x)' ≪ λ₃`);
* `g'(x) ≥ λ₂x` for `x ≥ 0` and `g'(x) ≤ λ₂x` for `x ≤ 0` (so `|g'(x)| ≥ λ₂|x|`).

Everything comes from one helper: if `F(0) = 0` and `|F'(t)| ≤ c|t|^k` on the segment from
`0` to `x`, then `|F(x)| ≤ c|x|^{k+1}/(k+1)`.
-/

open Real Finset intervalIntegral MeasureTheory

namespace LeanProofs.IntegerPoints

namespace SP

/-- The normalised data of Lemma 3.4. -/
structure Data where
  g : ℝ → ℝ
  a : ℝ
  b : ℝ
  lam₂ : ℝ
  lam₃ : ℝ
  lam₄ : ℝ
  ha : a < 0
  hb : 0 < b
  hlam₂ : 0 < lam₂
  hlam₃ : 0 < lam₃
  hlam₄ : 0 < lam₄
  hg : ContDiff ℝ 4 g
  hg0 : g 0 = 0
  hg'0 : deriv g 0 = 0
  h2 : ∀ x ∈ Set.Icc a b, lam₂ ≤ deriv (deriv g) x
  h3 : ∀ x ∈ Set.Icc a b, |deriv (deriv (deriv g)) x| ≤ lam₃
  h4 : ∀ x ∈ Set.Icc a b, |deriv (deriv (deriv (deriv g))) x| ≤ lam₄

namespace Data

variable (D : Data)

/-- `g'`. -/
noncomputable def g1 : ℝ → ℝ := deriv D.g
/-- `g''`. -/
noncomputable def g2 : ℝ → ℝ := deriv (deriv D.g)
/-- `g'''`. -/
noncomputable def g3 : ℝ → ℝ := deriv (deriv (deriv D.g))
/-- `g''''`. -/
noncomputable def g4 : ℝ → ℝ := deriv (deriv (deriv (deriv D.g)))

theorem contDiff_g1 : ContDiff ℝ 3 D.g1 :=
  (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (3 + 1) D.g from D.hg)).2.2
theorem contDiff_g2 : ContDiff ℝ 2 D.g2 :=
  (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (2 + 1) D.g1 from D.contDiff_g1)).2.2
theorem contDiff_g3 : ContDiff ℝ 1 D.g3 :=
  (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) D.g2 from D.contDiff_g2)).2.2
theorem continuous_g4 : Continuous D.g4 := D.contDiff_g3.continuous_deriv le_rfl

theorem continuous_g : Continuous D.g := D.hg.continuous
theorem continuous_g1 : Continuous D.g1 := D.contDiff_g1.continuous
theorem continuous_g2 : Continuous D.g2 := D.contDiff_g2.continuous
theorem continuous_g3 : Continuous D.g3 := D.contDiff_g3.continuous

theorem hasDerivAt_g (x : ℝ) : HasDerivAt D.g (D.g1 x) x :=
  ((D.hg.differentiable (by norm_num)) x).hasDerivAt
theorem hasDerivAt_g1 (x : ℝ) : HasDerivAt D.g1 (D.g2 x) x :=
  ((D.contDiff_g1.differentiable (by norm_num)) x).hasDerivAt
theorem hasDerivAt_g2 (x : ℝ) : HasDerivAt D.g2 (D.g3 x) x :=
  ((D.contDiff_g2.differentiable (by norm_num)) x).hasDerivAt
theorem hasDerivAt_g3 (x : ℝ) : HasDerivAt D.g3 (D.g4 x) x :=
  ((D.contDiff_g3.differentiable one_ne_zero) x).hasDerivAt

theorem g1_zero : D.g1 0 = 0 := D.hg'0

theorem g2_pos_at_zero : D.lam₂ ≤ D.g2 0 := D.h2 0 ⟨D.ha.le, D.hb.le⟩

/-! ### The remainder `r` -/

/-- `r(x) = g(x) − g''(0) x²/2`. -/
noncomputable def r (x : ℝ) : ℝ := D.g x - D.g2 0 * x ^ 2 / 2
/-- `r'(x) = g'(x) − g''(0) x`. -/
noncomputable def r1 (x : ℝ) : ℝ := D.g1 x - D.g2 0 * x
/-- `r''(x) = g''(x) − g''(0)`. -/
noncomputable def r2 (x : ℝ) : ℝ := D.g2 x - D.g2 0

theorem hasDerivAt_r (x : ℝ) : HasDerivAt D.r (D.r1 x) x := by
  unfold r r1
  have := (D.hasDerivAt_g x).sub (((hasDerivAt_id' x).pow 2).const_mul (D.g2 0) |>.div_const 2)
  refine this.congr_deriv ?_
  ring

theorem hasDerivAt_r1 (x : ℝ) : HasDerivAt D.r1 (D.r2 x) x := by
  unfold r1 r2
  have := (D.hasDerivAt_g1 x).sub ((hasDerivAt_id' x).const_mul (D.g2 0))
  refine this.congr_deriv ?_
  ring

theorem hasDerivAt_r2 (x : ℝ) : HasDerivAt D.r2 (D.g3 x) x := by
  unfold r2
  exact (D.hasDerivAt_g2 x).sub_const _

theorem r_zero : D.r 0 = 0 := by simp [r, D.hg0]
theorem r1_zero : D.r1 0 = 0 := by simp [r1, D.g1_zero]
theorem r2_zero : D.r2 0 = 0 := by simp [r2]

theorem continuous_r : Continuous D.r := by
  unfold r
  exact D.continuous_g.sub (by fun_prop)
theorem continuous_r1 : Continuous D.r1 := by
  unfold r1
  exact D.continuous_g1.sub (by fun_prop)
theorem continuous_r2 : Continuous D.r2 := D.continuous_g2.sub continuous_const

/-! ### The basic helper -/

/-- `∫_0^x |t|^k dt = x^{k+1}/(k+1)` for `x ≥ 0`. -/
theorem integral_abs_pow_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    ∫ t in (0 : ℝ)..x, |t| ^ k = x ^ (k + 1) / (k + 1) := by
  have : ∫ t in (0 : ℝ)..x, |t| ^ k = ∫ t in (0 : ℝ)..x, t ^ k := by
    apply integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    simp only
    rw [abs_of_nonneg ht.1]
  rw [this, integral_pow, zero_pow (Nat.succ_ne_zero k), sub_zero]

/-- `∫_x^0 |t|^k dt = (−x)^{k+1}/(k+1)` for `x ≤ 0`. -/
theorem integral_abs_pow_nonpos {x : ℝ} (hx : x ≤ 0) (k : ℕ) :
    ∫ t in x..(0 : ℝ), |t| ^ k = (-x) ^ (k + 1) / (k + 1) := by
  have h1 : ∫ t in x..(0 : ℝ), |t| ^ k = ∫ t in x..(0 : ℝ), (-t) ^ k := by
    apply integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    simp only
    rw [abs_of_nonpos ht.2]
  have h2 : ∫ t in x..(0 : ℝ), (-t) ^ k = ∫ s in (0 : ℝ)..(-x), s ^ k := by
    have := integral_comp_neg (a := x) (b := 0) (fun s : ℝ => s ^ k)
    simpa using this
  rw [h1, h2, integral_pow, zero_pow (Nat.succ_ne_zero k), sub_zero]

/-- If `F(0) = 0` and `|F'(t)| ≤ c |t|^k` on the segment from `0` to `x`, then
`|F(x)| ≤ c |x|^{k+1} / (k+1)`. -/
theorem abs_le_of_deriv_le_pow {F F' : ℝ → ℝ} (hF : ∀ t, HasDerivAt F (F' t) t)
    (hF'c : Continuous F') (hF0 : F 0 = 0) {c : ℝ} (hc : 0 ≤ c) {k : ℕ} {x : ℝ}
    (hb : ∀ t ∈ Set.uIcc 0 x, |F' t| ≤ c * |t| ^ k) :
    |F x| ≤ c * |x| ^ (k + 1) / (k + 1) := by
  have hFTC : ∫ t in (0 : ℝ)..x, F' t = F x - F 0 :=
    integral_eq_sub_of_hasDerivAt (fun t _ => hF t) (hF'c.intervalIntegrable _ _)
  rw [hF0, sub_zero] at hFTC
  rw [← hFTC]
  have hint : ∀ p q : ℝ, IntervalIntegrable (fun t : ℝ => c * |t| ^ k) volume p q :=
    fun p q => (by fun_prop : Continuous fun t : ℝ => c * |t| ^ k).intervalIntegrable p q
  rcases le_or_gt 0 x with hx | hx
  · have := norm_integral_le_of_norm_le (f := F') (μ := volume) hx
      (Filter.Eventually.of_forall fun t ht => by
        rw [Real.norm_eq_abs]
        exact hb t (by rw [Set.uIcc_of_le hx]; exact ⟨ht.1.le, ht.2⟩)) (hint 0 x)
    rw [Real.norm_eq_abs] at this
    refine this.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, integral_abs_pow_nonneg hx, abs_of_nonneg hx]
    ring
  · rw [integral_symm, abs_neg]
    have := norm_integral_le_of_norm_le (f := F') (μ := volume) hx.le
      (Filter.Eventually.of_forall fun t ht => by
        rw [Real.norm_eq_abs]
        exact hb t (by rw [Set.uIcc_of_ge hx.le]; exact ⟨ht.1.le, ht.2⟩)) (hint x 0)
    rw [Real.norm_eq_abs] at this
    refine this.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, integral_abs_pow_nonpos hx.le, abs_of_neg hx]
    ring

theorem uIcc_zero_subset {x : ℝ} (hx : x ∈ Set.Icc D.a D.b) : Set.uIcc 0 x ⊆ Set.Icc D.a D.b := by
  rcases le_or_gt 0 x with h | h
  · rw [Set.uIcc_of_le h]
    exact Set.Icc_subset_Icc D.ha.le hx.2
  · rw [Set.uIcc_of_ge h.le]
    exact Set.Icc_subset_Icc hx.1 D.hb.le

/-! ### The bounds on `r`, `r'`, `r''` -/

theorem abs_r2_le {x : ℝ} (hx : x ∈ Set.Icc D.a D.b) : |D.r2 x| ≤ D.lam₃ * |x| := by
  have := abs_le_of_deriv_le_pow (F := D.r2) (F' := D.g3) D.hasDerivAt_r2 D.continuous_g3
    D.r2_zero D.hlam₃.le (k := 0) (x := x) (fun t ht => by
      rw [pow_zero, mul_one]
      exact D.h3 t (D.uIcc_zero_subset hx ht))
  simpa using this

theorem abs_r1_le {x : ℝ} (hx : x ∈ Set.Icc D.a D.b) : |D.r1 x| ≤ D.lam₃ * x ^ 2 / 2 := by
  have := abs_le_of_deriv_le_pow (F := D.r1) (F' := D.r2) D.hasDerivAt_r1 D.continuous_r2
    D.r1_zero D.hlam₃.le (k := 1) (x := x) (fun t ht => by
      rw [pow_one]
      exact D.abs_r2_le (D.uIcc_zero_subset hx ht))
  norm_num at this
  exact this

theorem abs_r_le {x : ℝ} (hx : x ∈ Set.Icc D.a D.b) : |D.r x| ≤ D.lam₃ * |x| ^ 3 / 6 := by
  have := abs_le_of_deriv_le_pow (F := D.r) (F' := D.r1) D.hasDerivAt_r D.continuous_r1
    D.r_zero (c := D.lam₃ / 2) (by have := D.hlam₃; positivity) (k := 2) (x := x) (fun t ht => by
      have := D.abs_r1_le (D.uIcc_zero_subset hx ht)
      rw [sq_abs]
      linarith)
  refine this.trans (le_of_eq ?_)
  ring

/-! ### `Φ = x r'' − 2 r'` and `Ψ = x r' − 3 r` -/

/-- `E(t) = t g'''(t) − r''(t)`, with `E' = t g''''(t)`. -/
noncomputable def E (t : ℝ) : ℝ := t * D.g3 t - D.r2 t

theorem hasDerivAt_E (t : ℝ) : HasDerivAt D.E (t * D.g4 t) t := by
  unfold E
  have := ((hasDerivAt_id' t).mul (D.hasDerivAt_g3 t)).sub (D.hasDerivAt_r2 t)
  refine this.congr_deriv ?_
  ring

theorem E_zero : D.E 0 = 0 := by simp [E, D.r2_zero]

theorem abs_E_le {x : ℝ} (hx : x ∈ Set.Icc D.a D.b) : |D.E x| ≤ D.lam₄ * x ^ 2 / 2 := by
  have := abs_le_of_deriv_le_pow (F := D.E) (F' := fun t => t * D.g4 t) D.hasDerivAt_E
    (continuous_id.mul D.continuous_g4) D.E_zero D.hlam₄.le (k := 1) (x := x) (fun t ht => by
      rw [pow_one, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (D.h4 t (D.uIcc_zero_subset hx ht)) (abs_nonneg _))
  norm_num at this
  exact this

/-- `Φ(x) = x r''(x) − 2 r'(x)`. -/
noncomputable def Φ (x : ℝ) : ℝ := x * D.r2 x - 2 * D.r1 x

theorem hasDerivAt_Φ (x : ℝ) : HasDerivAt D.Φ (D.E x) x := by
  unfold Φ E
  have := ((hasDerivAt_id' x).mul (D.hasDerivAt_r2 x)).sub ((D.hasDerivAt_r1 x).const_mul 2)
  refine this.congr_deriv ?_
  ring

theorem Φ_zero : D.Φ 0 = 0 := by simp [Φ, D.r1_zero, D.r2_zero]

theorem continuous_E : Continuous D.E := by
  unfold E
  exact (continuous_id.mul D.continuous_g3).sub D.continuous_r2

theorem abs_Φ_le {x : ℝ} (hx : x ∈ Set.Icc D.a D.b) : |D.Φ x| ≤ D.lam₄ * |x| ^ 3 / 6 := by
  have := abs_le_of_deriv_le_pow (F := D.Φ) (F' := D.E) D.hasDerivAt_Φ D.continuous_E
    D.Φ_zero (c := D.lam₄ / 2) (by have := D.hlam₄; positivity) (k := 2) (x := x) (fun t ht => by
      have := D.abs_E_le (D.uIcc_zero_subset hx ht)
      rw [sq_abs]
      linarith)
  refine this.trans (le_of_eq ?_)
  ring

/-- `Ψ(x) = x r'(x) − 3 r(x)`. -/
noncomputable def Ψ (x : ℝ) : ℝ := x * D.r1 x - 3 * D.r x

theorem hasDerivAt_Ψ (x : ℝ) : HasDerivAt D.Ψ (D.Φ x) x := by
  unfold Ψ Φ
  have := ((hasDerivAt_id' x).mul (D.hasDerivAt_r1 x)).sub ((D.hasDerivAt_r x).const_mul 3)
  refine this.congr_deriv ?_
  ring

theorem Ψ_zero : D.Ψ 0 = 0 := by simp [Ψ, D.r_zero, D.r1_zero]

theorem continuous_Φ : Continuous D.Φ := by
  unfold Φ
  exact (continuous_id.mul D.continuous_r2).sub (continuous_const.mul D.continuous_r1)

theorem abs_Ψ_le {x : ℝ} (hx : x ∈ Set.Icc D.a D.b) : |D.Ψ x| ≤ D.lam₄ * x ^ 4 / 24 := by
  have := abs_le_of_deriv_le_pow (F := D.Ψ) (F' := D.Φ) D.hasDerivAt_Ψ D.continuous_Φ
    D.Ψ_zero (c := D.lam₄ / 6) (by have := D.hlam₄; positivity) (k := 3) (x := x) (fun t ht => by
      have := D.abs_Φ_le (D.uIcc_zero_subset hx ht)
      linarith)
  rw [show |x| ^ (3 + 1) = x ^ 4 by rw [show (3 + 1 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs]; ring]
    at this
  refine this.trans (le_of_eq ?_)
  ring

/-- `|x r''(x) − r'(x)| ≤ 3 λ₃ x² / 2`. -/
theorem abs_xr2_sub_r1_le {x : ℝ} (hx : x ∈ Set.Icc D.a D.b) :
    |x * D.r2 x - D.r1 x| ≤ 3 * D.lam₃ * x ^ 2 / 2 := by
  have h1 := D.abs_r2_le hx
  have h2 := D.abs_r1_le hx
  calc |x * D.r2 x - D.r1 x| ≤ |x * D.r2 x| + |D.r1 x| := abs_sub _ _
    _ = |x| * |D.r2 x| + |D.r1 x| := by rw [abs_mul]
    _ ≤ |x| * (D.lam₃ * |x|) + D.lam₃ * x ^ 2 / 2 :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) h2
    _ = 3 * D.lam₃ * x ^ 2 / 2 := by rw [← sq_abs x]; ring

/-! ### `g'` grows at least linearly -/

theorem g1_ge_of_nonneg {x : ℝ} (hx : x ∈ Set.Icc D.a D.b) (hx0 : 0 ≤ x) :
    D.lam₂ * x ≤ D.g1 x := by
  have hFTC : ∫ t in (0 : ℝ)..x, D.g2 t = D.g1 x - D.g1 0 :=
    integral_eq_sub_of_hasDerivAt (fun t _ => D.hasDerivAt_g1 t)
      (D.continuous_g2.intervalIntegrable _ _)
  rw [D.g1_zero, sub_zero] at hFTC
  rw [← hFTC]
  have := integral_mono_on (μ := volume) hx0 intervalIntegrable_const
    (D.continuous_g2.intervalIntegrable _ _)
    (fun t ht => D.h2 t ⟨D.ha.le.trans ht.1, ht.2.trans hx.2⟩)
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at this
  linarith

theorem g1_le_of_nonpos {x : ℝ} (hx : x ∈ Set.Icc D.a D.b) (hx0 : x ≤ 0) :
    D.g1 x ≤ D.lam₂ * x := by
  have hFTC : ∫ t in x..(0 : ℝ), D.g2 t = D.g1 0 - D.g1 x :=
    integral_eq_sub_of_hasDerivAt (fun t _ => D.hasDerivAt_g1 t)
      (D.continuous_g2.intervalIntegrable _ _)
  rw [D.g1_zero, zero_sub] at hFTC
  have := integral_mono_on (μ := volume) hx0 intervalIntegrable_const
    (D.continuous_g2.intervalIntegrable _ _)
    (fun t ht => D.h2 t ⟨hx.1.trans ht.1, ht.2.trans D.hb.le⟩)
  rw [intervalIntegral.integral_const, zero_sub, smul_eq_mul] at this
  linarith

theorem abs_g1_ge {x : ℝ} (hx : x ∈ Set.Icc D.a D.b) : D.lam₂ * |x| ≤ |D.g1 x| := by
  rcases le_or_gt 0 x with h | h
  · have := D.g1_ge_of_nonneg hx h
    rw [abs_of_nonneg h, abs_of_nonneg (by nlinarith [D.hlam₂])]
    exact this
  · have := D.g1_le_of_nonpos hx h.le
    rw [abs_of_neg h, abs_of_nonpos (by nlinarith [D.hlam₂])]
    linarith

theorem g1_ne_zero {x : ℝ} (hx : x ∈ Set.Icc D.a D.b) (hx0 : x ≠ 0) : D.g1 x ≠ 0 := by
  intro h
  have := D.abs_g1_ge hx
  rw [h, abs_zero] at this
  have : 0 < D.lam₂ * |x| := mul_pos D.hlam₂ (abs_pos.2 hx0)
  linarith

end Data

end SP

end LeanProofs.IntegerPoints
