import FabiusFunction.LobeLogFactorization
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Convex.Deriv

/-!
# Strict log-concavity inside every lobe

The side-lobe half of the audits' `thm:one-peak`: on any interval
`(u,v)` strictly inside the lobe `(m, m+1)`, the canonical log-series

`F(z) = ∑'_{(h,r)} log (1 − z²/(2ʰ(r+1))²)`

differentiates termwise twice and has strictly negative second
derivative, hence is strictly concave.  The lattice dichotomy
`a ≤ m ∨ m+1 ≤ a` gives the single uniform gap

`|a² − y²| ≥ lobeGap·a²` for all `y ∈ (u,v)`,

which powers both summable majorants at once.

* `lobeZero_le_or_add_one_le` — the integer dichotomy.
* `sq_gap` — the uniform quadratic gap.
* `hasDerivAt_lobe_log_series`, `hasDerivAt_lobe_log_deriv` — the two
  termwise derivatives.
* `strictConcaveOn_lobe_log_series` — **strict concavity**.
-/

set_option autoImplicit false

open Filter Topology Real Set

namespace Fabius

/-- The uniform relative gap between `y² (y ∈ (u,v))` and the squared
lattice, valid on both sides of the lobe `(m, m+1)`. -/
noncomputable def lobeGap (m : ℕ) (u v : ℝ) : ℝ :=
  min ((u ^ 2 - (m:ℝ) ^ 2) / ((m:ℝ) ^ 2 + 1))
    (1 - v ^ 2 / ((m:ℝ) + 1) ^ 2)

/-- The integer lattice avoids the open unit interval `(m, m+1)`. -/
theorem lobeZero_le_or_add_one_le (m : ℕ) (p : ℕ × ℕ) :
    lobeZero p ≤ (m:ℝ) ∨ ((m:ℝ) + 1) ≤ lobeZero p := by
  rcases Nat.lt_or_ge m (2 ^ p.1 * (p.2 + 1)) with h | h
  · right
    simp only [lobeZero]
    exact_mod_cast Nat.succ_le_of_lt h
  · left
    simp only [lobeZero]
    exact_mod_cast h

/-- If `m < u < v < m+1`, both relative gap terms are positive, so
`0 < lobeGap m u v`. -/
theorem lobeGap_pos {m : ℕ} {u v : ℝ} (hu : (m:ℝ) < u) (huv : u < v)
    (hv : v < (m:ℝ) + 1) : 0 < lobeGap m u v := by
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hu0 : 0 < u := lt_of_le_of_lt hm0 hu
  have hv0 : 0 < v := lt_trans hu0 huv
  apply lt_min
  · apply div_pos ?_ (by positivity)
    nlinarith
  · have hsq : v ^ 2 < ((m:ℝ) + 1) ^ 2 := by nlinarith
    have := (div_lt_one (by positivity :
      (0:ℝ) < ((m:ℝ) + 1) ^ 2)).mpr hsq
    linarith

/-- Points of `(u,v)` are not lattice values. -/
theorem lobeZero_ne_abs_of_mem {m : ℕ} {u v y : ℝ} (hu : (m:ℝ) < u)
    (hv : v < (m:ℝ) + 1) (hy : y ∈ Set.Ioo u v) (p : ℕ × ℕ) :
    lobeZero p ≠ |y| := by
  obtain ⟨hyu, hyv⟩ := hy
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hy0 : 0 < y := lt_trans (lt_of_le_of_lt hm0 hu) hyu
  rw [abs_of_pos hy0]
  rcases lobeZero_le_or_add_one_le m p with h | h
  · exact ne_of_lt (lt_of_le_of_lt h (lt_trans hu hyu))
  · exact ne_of_gt (lt_of_lt_of_le (lt_trans hyv hv) h)

/-- **The uniform quadratic gap**: for `y ∈ (u,v)` inside the lobe,
`lobeGap·a² ≤ |a² − y²|` at every lattice value `a`. -/
theorem sq_gap {m : ℕ} {u v y : ℝ} (hu : (m:ℝ) < u) (huv : u < v)
    (hv : v < (m:ℝ) + 1) (hy : y ∈ Set.Ioo u v) (p : ℕ × ℕ) :
    lobeGap m u v * (lobeZero p) ^ 2 ≤
      |(lobeZero p) ^ 2 - y ^ 2| := by
  obtain ⟨hyu, hyv⟩ := hy
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hu0 : 0 < u := lt_of_le_of_lt hm0 hu
  have hy0 : 0 < y := lt_trans hu0 hyu
  have hgap0 := lobeGap_pos hu huv hv
  have ha1 := one_le_lobeZero p
  have ha0 := lobeZero_pos p
  rcases lobeZero_le_or_add_one_le m p with hc | hc
  · -- exceptional side: `a ≤ m < u < y`, so `y² − a² ≥ u² − m²`
    have hd : (lobeZero p) ^ 2 - y ^ 2 < 0 := by nlinarith
    rw [abs_of_neg hd, neg_sub]
    have h1 : lobeGap m u v ≤
        (u ^ 2 - (m:ℝ) ^ 2) / ((m:ℝ) ^ 2 + 1) := min_le_left _ _
    have hsqa : (lobeZero p) ^ 2 ≤ (m:ℝ) ^ 2 + 1 := by nlinarith
    have h2 : lobeGap m u v * (lobeZero p) ^ 2 ≤
        lobeGap m u v * ((m:ℝ) ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left hsqa hgap0.le
    have h3 : lobeGap m u v * ((m:ℝ) ^ 2 + 1) ≤ u ^ 2 - (m:ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right h1
        (by positivity : (0:ℝ) ≤ (m:ℝ) ^ 2 + 1)
      calc lobeGap m u v * ((m:ℝ) ^ 2 + 1) ≤
          (u ^ 2 - (m:ℝ) ^ 2) / ((m:ℝ) ^ 2 + 1) *
            ((m:ℝ) ^ 2 + 1) := this
        _ = u ^ 2 - (m:ℝ) ^ 2 := by
            field_simp
    have h4 : u ^ 2 - (m:ℝ) ^ 2 ≤ y ^ 2 - (lobeZero p) ^ 2 := by
      nlinarith
    linarith
  · -- tail side: `y < v < m+1 ≤ a`, so `a² − y² ≥ a²·(1 − v²/(m+1)²)`
    have hva : v < lobeZero p := lt_of_lt_of_le hv hc
    have hd : 0 < (lobeZero p) ^ 2 - y ^ 2 := by nlinarith
    rw [abs_of_pos hd]
    have h1 : lobeGap m u v ≤ 1 - v ^ 2 / ((m:ℝ) + 1) ^ 2 :=
      min_le_right _ _
    have hm1 : (0:ℝ) < ((m:ℝ) + 1) ^ 2 := by positivity
    have hsq : ((m:ℝ) + 1) ^ 2 ≤ (lobeZero p) ^ 2 := by nlinarith
    -- `a²·(1 − v²/(m+1)²) ≤ a² − v²` since `a² ≥ (m+1)²`
    have hkey : (lobeZero p) ^ 2 * (1 - v ^ 2 / ((m:ℝ) + 1) ^ 2) ≤
        (lobeZero p) ^ 2 - v ^ 2 := by
      have hdivle : v ^ 2 / ((m:ℝ) + 1) ^ 2 * ((m:ℝ) + 1) ^ 2 =
          v ^ 2 := by field_simp
      have hexp : (lobeZero p) ^ 2 *
          (1 - v ^ 2 / ((m:ℝ) + 1) ^ 2) =
          (lobeZero p) ^ 2 -
            (lobeZero p) ^ 2 * (v ^ 2 / ((m:ℝ) + 1) ^ 2) := by ring
      rw [hexp]
      have hmono : v ^ 2 ≤
          (lobeZero p) ^ 2 * (v ^ 2 / ((m:ℝ) + 1) ^ 2) := by
        have := mul_le_mul_of_nonneg_right hsq
          (by positivity : (0:ℝ) ≤ v ^ 2 / ((m:ℝ) + 1) ^ 2)
        calc v ^ 2 = ((m:ℝ) + 1) ^ 2 * (v ^ 2 / ((m:ℝ) + 1) ^ 2) := by
              field_simp
          _ ≤ (lobeZero p) ^ 2 * (v ^ 2 / ((m:ℝ) + 1) ^ 2) := this
      linarith
    have h2 : lobeGap m u v * (lobeZero p) ^ 2 ≤
        (1 - v ^ 2 / ((m:ℝ) + 1) ^ 2) * (lobeZero p) ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h4 : (lobeZero p) ^ 2 - v ^ 2 ≤
        (lobeZero p) ^ 2 - y ^ 2 := by nlinarith
    nlinarith [hkey]

/-- Per-factor derivative at any point where the factor is nonzero. -/
theorem hasDerivAt_factor_of_ne (p : ℕ × ℕ) {y : ℝ}
    (hy : 1 - y ^ 2 / (lobeZero p) ^ 2 ≠ 0) :
    HasDerivAt (fun z => Real.log (1 - z ^ 2 / (lobeZero p) ^ 2))
      (-(2 * y) / ((lobeZero p) ^ 2 - y ^ 2)) y := by
  have ha := one_le_sq_lobeZero p
  have ha0 : ((lobeZero p) ^ 2) ≠ 0 := by positivity
  have hden : (lobeZero p) ^ 2 - y ^ 2 ≠ 0 := by
    intro h0
    apply hy
    have hyy : y ^ 2 = (lobeZero p) ^ 2 := by linarith
    rw [hyy, div_self ha0]
    ring
  have hpow : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
    simpa using hasDerivAt_pow 2 y
  have hdiv : HasDerivAt (fun z : ℝ => z ^ 2 / (lobeZero p) ^ 2)
      (2 * y / (lobeZero p) ^ 2) y := hpow.div_const _
  have hsub : HasDerivAt
      (fun z : ℝ => 1 - z ^ 2 / (lobeZero p) ^ 2)
      (-(2 * y / (lobeZero p) ^ 2)) y := hdiv.const_sub 1
  have hlog := hsub.log hy
  have hval : -(2 * y / (lobeZero p) ^ 2) /
      (1 - y ^ 2 / (lobeZero p) ^ 2) =
      -(2 * y) / ((lobeZero p) ^ 2 - y ^ 2) := by
    have hinv : (lobeZero p) ^ 2 * ((lobeZero p) ^ 2)⁻¹ = 1 :=
      mul_inv_cancel₀ ha0
    have hdd : ∀ b : ℝ, b / (lobeZero p) ^ 2 =
        b * ((lobeZero p) ^ 2)⁻¹ := fun b => div_eq_mul_inv _ _
    rw [div_eq_div_iff hy hden, hdd (2 * y), hdd (y ^ 2)]
    linear_combination (-(2 * y)) * hinv
  rwa [hval] at hlog

/-- Factors are nonzero throughout `(u,v)`. -/
theorem factor_ne_zero_of_mem_lobe {m : ℕ} {u v y : ℝ}
    (hu : (m:ℝ) < u) (hv : v < (m:ℝ) + 1) (hy : y ∈ Set.Ioo u v)
    (p : ℕ × ℕ) : 1 - y ^ 2 / (lobeZero p) ^ 2 ≠ 0 :=
  factor_ne_zero_of_ne (lobeZero_ne_abs_of_mem hu hv hy p)

/-- The first-derivative majorant on `(u,v)`. -/
theorem side_deriv_bound {m : ℕ} {u v y : ℝ} (hu : (m:ℝ) < u)
    (huv : u < v) (hv : v < (m:ℝ) + 1) (hy : y ∈ Set.Ioo u v)
    (p : ℕ × ℕ) :
    ‖-(2 * y) / ((lobeZero p) ^ 2 - y ^ 2)‖ ≤
      (2 * v / lobeGap m u v) * (1 / (lobeZero p) ^ 2) := by
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hu0 : 0 < u := lt_of_le_of_lt hm0 hu
  have hy0 : 0 < y := lt_trans hu0 hy.1
  have hyv : y < v := hy.2
  have hgap0 := lobeGap_pos hu huv hv
  have ha0 := lobeZero_pos p
  have hgap := sq_gap hu huv hv hy p
  have hD0 : 0 < |(lobeZero p) ^ 2 - y ^ 2| := by
    calc (0:ℝ) < lobeGap m u v * (lobeZero p) ^ 2 := by positivity
      _ ≤ _ := hgap
  rw [Real.norm_eq_abs, abs_div, abs_neg,
    abs_of_pos (by positivity : (0:ℝ) < 2 * y),
    show (2 * v / lobeGap m u v) * (1 / (lobeZero p) ^ 2) =
      2 * v / (lobeGap m u v * (lobeZero p) ^ 2) by
        rw [mul_one_div, div_div],
    div_le_div_iff₀ hD0 (by positivity)]
  have h1 : 2 * y * (lobeGap m u v * (lobeZero p) ^ 2) ≤
      2 * v * (lobeGap m u v * (lobeZero p) ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h2 : 2 * v * (lobeGap m u v * (lobeZero p) ^ 2) ≤
      2 * v * |(lobeZero p) ^ 2 - y ^ 2| :=
    mul_le_mul_of_nonneg_left hgap (by linarith)
  linarith

/-- The second-derivative majorant on `(u,v)`. -/
theorem side_deriv2_bound {m : ℕ} {u v y : ℝ} (hu : (m:ℝ) < u)
    (huv : u < v) (hv : v < (m:ℝ) + 1) (hy : y ∈ Set.Ioo u v)
    (p : ℕ × ℕ) :
    ‖-(2 * ((lobeZero p) ^ 2 + y ^ 2)) /
        ((lobeZero p) ^ 2 - y ^ 2) ^ 2‖ ≤
      (2 * (1 + v ^ 2) / (lobeGap m u v) ^ 2) *
        (1 / (lobeZero p) ^ 2) := by
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hu0 : 0 < u := lt_of_le_of_lt hm0 hu
  have hy0 : 0 < y := lt_trans hu0 hy.1
  have hyv : y < v := hy.2
  have hgap0 := lobeGap_pos hu huv hv
  have ha0 := lobeZero_pos p
  have ha1 := one_le_sq_lobeZero p
  have hgap := sq_gap hu huv hv hy p
  have hD0 : 0 < |(lobeZero p) ^ 2 - y ^ 2| := by
    calc (0:ℝ) < lobeGap m u v * (lobeZero p) ^ 2 := by positivity
      _ ≤ _ := hgap
  have hDsq : ((lobeZero p) ^ 2 - y ^ 2) ^ 2 =
      |(lobeZero p) ^ 2 - y ^ 2| ^ 2 := (sq_abs _).symm
  have hDsq0 : 0 < ((lobeZero p) ^ 2 - y ^ 2) ^ 2 := by
    rw [hDsq]
    positivity
  rw [Real.norm_eq_abs, abs_div, abs_neg,
    abs_of_pos (by positivity :
      (0:ℝ) < 2 * ((lobeZero p) ^ 2 + y ^ 2)),
    abs_of_pos hDsq0,
    show (2 * (1 + v ^ 2) / (lobeGap m u v) ^ 2) *
        (1 / (lobeZero p) ^ 2) =
      2 * (1 + v ^ 2) /
        ((lobeGap m u v) ^ 2 * (lobeZero p) ^ 2) by
        rw [mul_one_div, div_div],
    div_le_div_iff₀ hDsq0 (by positivity)]
  -- numerator: `a² + y² ≤ (1 + v²)·a²` since `1 ≤ a²`, `y ≤ v`
  have hnum : (lobeZero p) ^ 2 + y ^ 2 ≤
      (1 + v ^ 2) * (lobeZero p) ^ 2 := by nlinarith
  -- denominator: `(gap·a²)² ≤ (a² − y²)²`
  have hsq : (lobeGap m u v * (lobeZero p) ^ 2) ^ 2 ≤
      ((lobeZero p) ^ 2 - y ^ 2) ^ 2 := by
    rw [hDsq]
    exact pow_le_pow_left₀ (by positivity) hgap 2
  have h1 : 2 * ((lobeZero p) ^ 2 + y ^ 2) *
      ((lobeGap m u v) ^ 2 * (lobeZero p) ^ 2) ≤
      2 * ((1 + v ^ 2) * (lobeZero p) ^ 2) *
        ((lobeGap m u v) ^ 2 * (lobeZero p) ^ 2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by positivity)
    linarith
  have h2 : 2 * (1 + v ^ 2) *
      (lobeGap m u v * (lobeZero p) ^ 2) ^ 2 ≤
      2 * (1 + v ^ 2) * ((lobeZero p) ^ 2 - y ^ 2) ^ 2 := by
    apply mul_le_mul_of_nonneg_left hsq
    positivity
  have h3 : 2 * ((1 + v ^ 2) * (lobeZero p) ^ 2) *
      ((lobeGap m u v) ^ 2 * (lobeZero p) ^ 2) =
      2 * (1 + v ^ 2) *
        (lobeGap m u v * (lobeZero p) ^ 2) ^ 2 := by ring
  linarith

/-- **First termwise derivative** inside the lobe. -/
theorem hasDerivAt_lobe_log_series {m : ℕ} {u v x : ℝ}
    (hu : (m:ℝ) < u) (huv : u < v) (hv : v < (m:ℝ) + 1)
    (hx : x ∈ Set.Ioo u v) :
    HasDerivAt (fun z => ∑' p : ℕ × ℕ,
      Real.log (1 - z ^ 2 / (lobeZero p) ^ 2))
      (∑' p : ℕ × ℕ, -(2 * x) / ((lobeZero p) ^ 2 - x ^ 2)) x := by
  apply hasDerivAt_tsum_of_isPreconnected
    (u := fun p => (2 * v / lobeGap m u v) * (1 / (lobeZero p) ^ 2))
    (summable_inv_sq_lobeZero.mul_left _)
    (isOpen_Ioo (a := u) (b := v))
    ((convex_Ioo u v).isPreconnected)
    (fun p y hy => hasDerivAt_factor_of_ne p
      (factor_ne_zero_of_mem_lobe hu hv hy p))
    (fun p y hy => side_deriv_bound hu huv hv hy p)
    (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)
    (summable_log_lobe_factors ((u + v) / 2))
    hx

/-- **Second termwise derivative** inside the lobe. -/
theorem hasDerivAt_lobe_log_deriv {m : ℕ} {u v x : ℝ}
    (hu : (m:ℝ) < u) (huv : u < v) (hv : v < (m:ℝ) + 1)
    (hx : x ∈ Set.Ioo u v) :
    HasDerivAt (fun z => ∑' p : ℕ × ℕ,
      -(2 * z) / ((lobeZero p) ^ 2 - z ^ 2))
      (∑' p : ℕ × ℕ, -(2 * ((lobeZero p) ^ 2 + x ^ 2)) /
        ((lobeZero p) ^ 2 - x ^ 2) ^ 2) x := by
  have hmid : (u + v) / 2 ∈ Set.Ioo u v :=
    Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  apply hasDerivAt_tsum_of_isPreconnected
    (u := fun p => (2 * (1 + v ^ 2) / (lobeGap m u v) ^ 2) *
      (1 / (lobeZero p) ^ 2))
    (summable_inv_sq_lobeZero.mul_left _)
    (isOpen_Ioo (a := u) (b := v))
    ((convex_Ioo u v).isPreconnected)
    (fun p y hy => hasDerivAt_log_sq_sub_sq_deriv (lobeZero p) y (by
      have hgap := sq_gap hu huv hv hy p
      have hgap0 := lobeGap_pos hu huv hv
      have ha0 := lobeZero_pos p
      have hD0 : 0 < |(lobeZero p) ^ 2 - y ^ 2| := by
        calc (0:ℝ) < lobeGap m u v * (lobeZero p) ^ 2 := by
              positivity
          _ ≤ _ := hgap
      exact abs_pos.mp hD0))
    (fun p y hy => side_deriv2_bound hu huv hv hy p)
    hmid
    (Summable.of_norm_bounded
      (summable_inv_sq_lobeZero.mul_left
        (2 * v / lobeGap m u v))
      (fun p => side_deriv_bound hu huv hv hmid p))
    hx

/-- **Strict negativity of the second-derivative sum** inside the
lobe. -/
theorem lobe_log_second_deriv_neg {m : ℕ} {u v x : ℝ}
    (hu : (m:ℝ) < u) (huv : u < v) (hv : v < (m:ℝ) + 1)
    (hx : x ∈ Set.Ioo u v) :
    (∑' p : ℕ × ℕ, -(2 * ((lobeZero p) ^ 2 + x ^ 2)) /
      ((lobeZero p) ^ 2 - x ^ 2) ^ 2) < 0 := by
  have hgap0 := lobeGap_pos hu huv hv
  have hDpos : ∀ p : ℕ × ℕ,
      0 < ((lobeZero p) ^ 2 - x ^ 2) ^ 2 := by
    intro p
    have hgap := sq_gap hu huv hv hx p
    have ha0 := lobeZero_pos p
    have hD0 : 0 < |(lobeZero p) ^ 2 - x ^ 2| := by
      calc (0:ℝ) < lobeGap m u v * (lobeZero p) ^ 2 := by positivity
        _ ≤ _ := hgap
    rw [show ((lobeZero p) ^ 2 - x ^ 2) ^ 2 =
      |(lobeZero p) ^ 2 - x ^ 2| ^ 2 from (sq_abs _).symm]
    positivity
  have hsummable : Summable (fun p : ℕ × ℕ =>
      2 * ((lobeZero p) ^ 2 + x ^ 2) /
        ((lobeZero p) ^ 2 - x ^ 2) ^ 2) := by
    apply Summable.of_norm_bounded
      (summable_inv_sq_lobeZero.mul_left
        (2 * (1 + v ^ 2) / (lobeGap m u v) ^ 2))
    intro p
    have h := side_deriv2_bound hu huv hv hx p
    rw [Real.norm_eq_abs] at h ⊢
    rwa [show -(2 * ((lobeZero p) ^ 2 + x ^ 2)) /
        ((lobeZero p) ^ 2 - x ^ 2) ^ 2 =
        -(2 * ((lobeZero p) ^ 2 + x ^ 2) /
          ((lobeZero p) ^ 2 - x ^ 2) ^ 2) from neg_div _ _,
      abs_neg] at h
  have hpos : 0 < ∑' p : ℕ × ℕ,
      2 * ((lobeZero p) ^ 2 + x ^ 2) /
        ((lobeZero p) ^ 2 - x ^ 2) ^ 2 := by
    apply hsummable.tsum_pos (fun p => by positivity)
      ((0, 0) : ℕ × ℕ)
    apply div_pos
    · nlinarith [one_le_sq_lobeZero ((0, 0) : ℕ × ℕ), sq_nonneg x]
    · exact hDpos ((0, 0) : ℕ × ℕ)
  have hneg : (fun p : ℕ × ℕ =>
      -(2 * ((lobeZero p) ^ 2 + x ^ 2)) /
        ((lobeZero p) ^ 2 - x ^ 2) ^ 2) =
      fun p => -(2 * ((lobeZero p) ^ 2 + x ^ 2) /
        ((lobeZero p) ^ 2 - x ^ 2) ^ 2) := by
    funext p
    rw [neg_div]
  rw [hneg, tsum_neg]
  linarith

/-- **Strict log-concavity inside every lobe**: the canonical
log-series is strictly concave on any `(u,v)` with
`m < u < v < m+1`. -/
theorem strictConcaveOn_lobe_log_series (m : ℕ) {u v : ℝ}
    (hu : (m:ℝ) < u) (huv : u < v) (hv : v < (m:ℝ) + 1) :
    StrictConcaveOn ℝ (Set.Ioo u v)
      (fun z => ∑' p : ℕ × ℕ,
        Real.log (1 - z ^ 2 / (lobeZero p) ^ 2)) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ioo _ _)
  · intro x hx
    exact (hasDerivAt_lobe_log_series hu huv hv
      hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    show deriv (deriv (fun z => ∑' p : ℕ × ℕ,
      Real.log (1 - z ^ 2 / (lobeZero p) ^ 2))) x < 0
    have hEv : deriv (fun z => ∑' p : ℕ × ℕ,
        Real.log (1 - z ^ 2 / (lobeZero p) ^ 2)) =ᶠ[𝓝 x]
        (fun z => ∑' p : ℕ × ℕ,
          -(2 * z) / ((lobeZero p) ^ 2 - z ^ 2)) := by
      have hnhds : Set.Ioo u v ∈ 𝓝 x :=
        Ioo_mem_nhds (Set.mem_Ioo.mp hx).1 (Set.mem_Ioo.mp hx).2
      filter_upwards [hnhds] with y hy
      exact (hasDerivAt_lobe_log_series hu huv hv hy).deriv
    rw [hEv.deriv_eq, (hasDerivAt_lobe_log_deriv hu huv hv hx).deriv]
    exact lobe_log_second_deriv_neg hu huv hv hx

end Fabius
