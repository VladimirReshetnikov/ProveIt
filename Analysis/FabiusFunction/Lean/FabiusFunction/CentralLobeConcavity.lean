import FabiusFunction.LogFactorConcavity
import FabiusFunction.SincCanonicalProduct
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Convex.Deriv

/-!
# Strict log-concavity on the central lobe

The analytic half of the audits' one-peak theorem (`thm:one-peak`),
completed on the central lobe: the logarithm of the dyadic canonical
product,

`F(z) = ∑'_{(h,r)} log (1 − z²/(2ʰ(r+1))²)`,

differentiates termwise twice on `(−1,1)` (uniform summable bounds on
every `|z| ≤ β < 1`, via `hasDerivAt_tsum_of_isPreconnected`), its
second derivative is a sum of strictly negative terms
(`LogFactorConcavity`), and therefore

**`F` is strictly concave on `(−1,1)`** — the log of `|Φ|` has a
single peak on the central lobe.

* `lobeZero`, `one_le_lobeZero`, `summable_inv_sq_lobeZero` — the
  zero lattice and its master summability.
* `hasDerivAt_central_log_series` — first termwise derivative.
* `hasDerivAt_central_log_deriv` — second termwise derivative.
* `central_log_second_deriv_neg` — strict negativity.
* `strictConcaveOn_central_log_series` — **strict concavity**.
-/

set_option autoImplicit false

open Filter Topology Real Set

namespace Fabius

/-- The dyadic zero lattice `2ʰ(r+1)`, as a real number. -/
noncomputable def lobeZero (p : ℕ × ℕ) : ℝ :=
  ((2 ^ p.1 * (p.2 + 1) : ℕ) : ℝ)

/-- Every dyadic lattice value `lobeZero p = 2^{p.1}(p.2+1)` is at least `1`. -/
theorem one_le_lobeZero (p : ℕ × ℕ) : 1 ≤ lobeZero p := by
  rw [lobeZero]
  have h : 0 < 2 ^ p.1 * (p.2 + 1) := by positivity
  exact_mod_cast Nat.succ_le_of_lt h

/-- Every dyadic lattice value is strictly positive. -/
theorem lobeZero_pos (p : ℕ × ℕ) : 0 < lobeZero p :=
  lt_of_lt_of_le one_pos (one_le_lobeZero p)

/-- The square of every dyadic lattice value is at least `1`. -/
theorem one_le_sq_lobeZero (p : ℕ × ℕ) : 1 ≤ (lobeZero p) ^ 2 := by
  have h := one_le_lobeZero p
  nlinarith

/-- Master summability: `∑ 1/(2ʰ(r+1))² < ∞` (geometric × Basel). -/
theorem summable_inv_sq_lobeZero :
    Summable fun p : ℕ × ℕ => 1 / (lobeZero p) ^ 2 := by
  have hgeo : Summable fun h : ℕ => ((1:ℝ) / 4) ^ h :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hp2 : Summable fun r : ℕ => ((1:ℝ) / ((r + 1) ^ 2)) := by
    have h := Real.summable_one_div_nat_pow.mpr one_lt_two
    exact_mod_cast (summable_nat_add_iff 1).mpr h
  have hprod := hgeo.mul_of_nonneg hp2
    (fun h => by positivity) (fun r => by positivity)
  refine hprod.congr fun p => ?_
  obtain ⟨h, r⟩ := p
  show ((1:ℝ) / 4) ^ h * (1 / ((r:ℝ) + 1) ^ 2) =
    1 / (lobeZero (h, r)) ^ 2
  rw [lobeZero]
  push_cast
  rw [mul_pow, show ((2:ℝ) ^ h) ^ 2 = 4 ^ h by
    rw [← pow_mul, mul_comm h 2, pow_mul]; norm_num]
  rw [div_pow, one_pow]
  field_simp

/-- On `|z| < 1` every factor argument is positive. -/
theorem factor_pos {z : ℝ} (hz : |z| < 1) (p : ℕ × ℕ) :
    0 < 1 - z ^ 2 / (lobeZero p) ^ 2 := by
  have h1 := abs_lt.mp hz
  have hz2 : z ^ 2 < 1 := by nlinarith
  have ha := one_le_sq_lobeZero p
  have hdiv : z ^ 2 / (lobeZero p) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  linarith

/-- The per-factor derivative. -/
theorem hasDerivAt_factor (p : ℕ × ℕ) {y : ℝ} (hy : |y| < 1) :
    HasDerivAt (fun z => Real.log (1 - z ^ 2 / (lobeZero p) ^ 2))
      (-(2 * y) / ((lobeZero p) ^ 2 - y ^ 2)) y := by
  have ha := one_le_sq_lobeZero p
  have ha0 : ((lobeZero p) ^ 2) ≠ 0 := by positivity
  have hpos := factor_pos hy p
  have hpow : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
    simpa using hasDerivAt_pow 2 y
  have hdiv : HasDerivAt (fun z : ℝ => z ^ 2 / (lobeZero p) ^ 2)
      (2 * y / (lobeZero p) ^ 2) y := hpow.div_const _
  have hsub : HasDerivAt
      (fun z : ℝ => 1 - z ^ 2 / (lobeZero p) ^ 2)
      (-(2 * y / (lobeZero p) ^ 2)) y := hdiv.const_sub 1
  have hlog := hsub.log hpos.ne'
  have hval : -(2 * y / (lobeZero p) ^ 2) /
      (1 - y ^ 2 / (lobeZero p) ^ 2) =
      -(2 * y) / ((lobeZero p) ^ 2 - y ^ 2) := by
    have hden : (lobeZero p) ^ 2 - y ^ 2 ≠ 0 := by
      have h1 := abs_lt.mp hy
      have : y ^ 2 < 1 := by nlinarith
      nlinarith
    have hinv : (lobeZero p) ^ 2 * ((lobeZero p) ^ 2)⁻¹ = 1 :=
      mul_inv_cancel₀ ha0
    have hdd : ∀ b : ℝ, b / (lobeZero p) ^ 2 =
        b * ((lobeZero p) ^ 2)⁻¹ := fun b => div_eq_mul_inv _ _
    rw [div_eq_div_iff hpos.ne' hden, hdd (2 * y), hdd (y ^ 2)]
    linear_combination (-(2 * y)) * hinv
  rwa [hval] at hlog

/-- **First termwise derivative** on the central lobe. -/
theorem hasDerivAt_central_log_series {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (fun z => ∑' p : ℕ × ℕ,
      Real.log (1 - z ^ 2 / (lobeZero p) ^ 2))
      (∑' p : ℕ × ℕ, -(2 * x) / ((lobeZero p) ^ 2 - x ^ 2)) x := by
  set β : ℝ := (1 + |x|) / 2 with hβ
  have hxβ : |x| < β := by
    rw [hβ]
    have := abs_nonneg x
    linarith [hx]
  have hβ1 : β < 1 := by
    rw [hβ]
    linarith [hx]
  have hβ0 : 0 < β := by
    rw [hβ]
    have := abs_nonneg x
    linarith
  have hβsq : β ^ 2 < 1 := by nlinarith
  apply hasDerivAt_tsum_of_isPreconnected
    (u := fun p => (2 * β / (1 - β ^ 2)) * (1 / (lobeZero p) ^ 2))
    (summable_inv_sq_lobeZero.mul_left _) (isOpen_Ioo (a := -β) (b := β))
    ((convex_Ioo (-β) β).isPreconnected)
    (fun p y hy => hasDerivAt_factor p (by
      rw [Set.mem_Ioo] at hy
      rw [abs_lt]
      constructor
      · linarith [hy.1, hβ1]
      · linarith [hy.2, hβ1]))
    ?_ (Set.mem_Ioo.mpr ⟨by linarith, hβ0⟩) ?_
    (Set.mem_Ioo.mpr ⟨(abs_lt.mp hxβ).1, (abs_lt.mp hxβ).2⟩)
  · intro p y hy
    rw [Set.mem_Ioo] at hy
    have hyβ : |y| < β := abs_lt.mpr ⟨hy.1, hy.2⟩
    have hy2 : y ^ 2 < β ^ 2 := by
      nlinarith [abs_nonneg y, abs_lt.mp hyβ, sq_abs y]
    have ha := one_le_sq_lobeZero p
    have hdenpos : 0 < (lobeZero p) ^ 2 - y ^ 2 := by nlinarith
    have h1βpos : (0:ℝ) < 1 - β ^ 2 := by nlinarith
    have h2 : (lobeZero p) ^ 2 * (1 - β ^ 2) ≤
        (lobeZero p) ^ 2 - y ^ 2 := by nlinarith
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_mul,
      show |(2:ℝ)| = 2 by norm_num, abs_of_pos hdenpos,
      mul_one_div, div_le_div_iff₀ hdenpos
        (by positivity : (0:ℝ) < (lobeZero p) ^ 2),
      div_mul_eq_mul_div, le_div_iff₀ h1βpos]
    have hstep1 : 2 * |y| * ((lobeZero p) ^ 2 * (1 - β ^ 2)) ≤
        2 * β * ((lobeZero p) ^ 2 * (1 - β ^ 2)) := by
      apply mul_le_mul_of_nonneg_right (by linarith [hyβ.le])
      exact mul_nonneg (by positivity) (by linarith)
    have hstep2 : 2 * β * ((lobeZero p) ^ 2 * (1 - β ^ 2)) ≤
        2 * β * ((lobeZero p) ^ 2 - y ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    calc 2 * |y| * (lobeZero p) ^ 2 * (1 - β ^ 2) =
        2 * |y| * ((lobeZero p) ^ 2 * (1 - β ^ 2)) := by ring
      _ ≤ 2 * β * ((lobeZero p) ^ 2 * (1 - β ^ 2)) := hstep1
      _ ≤ 2 * β * ((lobeZero p) ^ 2 - y ^ 2) := hstep2
  · have hzero : (fun p : ℕ × ℕ =>
        Real.log (1 - (0:ℝ) ^ 2 / (lobeZero p) ^ 2)) =
        fun _ => (0:ℝ) := by
      funext p
      norm_num
    rw [hzero]
    exact summable_zero

/-- **Second termwise derivative** on the central lobe. -/
theorem hasDerivAt_central_log_deriv {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (fun z => ∑' p : ℕ × ℕ,
      -(2 * z) / ((lobeZero p) ^ 2 - z ^ 2))
      (∑' p : ℕ × ℕ, -(2 * ((lobeZero p) ^ 2 + x ^ 2)) /
        ((lobeZero p) ^ 2 - x ^ 2) ^ 2) x := by
  set β : ℝ := (1 + |x|) / 2 with hβ
  have hxβ : |x| < β := by
    rw [hβ]
    linarith [hx]
  have hβ1 : β < 1 := by
    rw [hβ]
    linarith [hx]
  have hβ0 : 0 < β := by
    rw [hβ]
    have := abs_nonneg x
    linarith
  have hβsq : β ^ 2 < 1 := by nlinarith
  apply hasDerivAt_tsum_of_isPreconnected
    (u := fun p => (4 / (1 - β ^ 2) ^ 2) * (1 / (lobeZero p) ^ 2))
    (summable_inv_sq_lobeZero.mul_left _)
    (isOpen_Ioo (a := -β) (b := β))
    ((convex_Ioo (-β) β).isPreconnected)
    (fun p y hy => hasDerivAt_log_sq_sub_sq_deriv (lobeZero p) y (by
      rw [Set.mem_Ioo] at hy
      have hyβ : |y| < β := abs_lt.mpr ⟨hy.1, hy.2⟩
      have hy1 : |y| < 1 := lt_trans hyβ hβ1
      have ha := one_le_sq_lobeZero p
      have h1 := abs_lt.mp hy1
      have hsq : y ^ 2 < 1 := by nlinarith
      nlinarith))
    ?_ (Set.mem_Ioo.mpr ⟨by linarith, hβ0⟩) ?_
    (Set.mem_Ioo.mpr ⟨(abs_lt.mp hxβ).1, (abs_lt.mp hxβ).2⟩)
  · intro p y hy
    rw [Set.mem_Ioo] at hy
    have hyβ : |y| < β := abs_lt.mpr ⟨hy.1, hy.2⟩
    have hy2 : y ^ 2 < β ^ 2 := by
      nlinarith [abs_nonneg y, abs_lt.mp hyβ, sq_abs y]
    have ha := one_le_sq_lobeZero p
    have hgap : (lobeZero p) ^ 2 * (1 - β ^ 2) ≤
        (lobeZero p) ^ 2 - y ^ 2 := by nlinarith
    have hgap0 : 0 < (lobeZero p) ^ 2 * (1 - β ^ 2) := by
      have : (0:ℝ) < 1 - β ^ 2 := by linarith
      positivity
    have hdenpos : 0 < (lobeZero p) ^ 2 - y ^ 2 := by linarith
    have hnum : 2 * ((lobeZero p) ^ 2 + y ^ 2) ≤
        4 * (lobeZero p) ^ 2 := by nlinarith
    have h1β : (1:ℝ) - β ^ 2 ≠ 0 := by nlinarith
    have ha0 : ((lobeZero p) ^ 2) ≠ 0 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_pos (by positivity : (0:ℝ) <
        2 * ((lobeZero p) ^ 2 + y ^ 2)),
      abs_of_pos (by positivity : (0:ℝ) <
        ((lobeZero p) ^ 2 - y ^ 2) ^ 2)]
    rw [div_le_iff₀ (by positivity :
      (0:ℝ) < ((lobeZero p) ^ 2 - y ^ 2) ^ 2)]
    have hsq : ((lobeZero p) ^ 2 * (1 - β ^ 2)) ^ 2 ≤
        ((lobeZero p) ^ 2 - y ^ 2) ^ 2 := by nlinarith
    calc 2 * ((lobeZero p) ^ 2 + y ^ 2) ≤ 4 * (lobeZero p) ^ 2 := hnum
      _ = (4 / (1 - β ^ 2) ^ 2) * (1 / (lobeZero p) ^ 2) *
          ((lobeZero p) ^ 2 * (1 - β ^ 2)) ^ 2 := by
          field_simp
      _ ≤ (4 / (1 - β ^ 2) ^ 2) * (1 / (lobeZero p) ^ 2) *
          ((lobeZero p) ^ 2 - y ^ 2) ^ 2 := by
          apply mul_le_mul_of_nonneg_left hsq (by positivity)
  · have hzero : (fun p : ℕ × ℕ =>
        -(2 * (0:ℝ)) / ((lobeZero p) ^ 2 - (0:ℝ) ^ 2)) =
        fun _ => (0:ℝ) := by
      funext p
      norm_num
    rw [hzero]
    exact summable_zero

/-- **Strict negativity of the second derivative sum**. -/
theorem central_log_second_deriv_neg {x : ℝ} (hx : |x| < 1) :
    (∑' p : ℕ × ℕ, -(2 * ((lobeZero p) ^ 2 + x ^ 2)) /
      ((lobeZero p) ^ 2 - x ^ 2) ^ 2) < 0 := by
  have h1 := abs_lt.mp hx
  have hx2 : x ^ 2 < 1 := by nlinarith
  have hden : ∀ p : ℕ × ℕ, 0 < (lobeZero p) ^ 2 - x ^ 2 := by
    intro p
    have := one_le_sq_lobeZero p
    nlinarith
  -- summability of the (positive) negations by domination
  have hsummable : Summable (fun p : ℕ × ℕ =>
      2 * ((lobeZero p) ^ 2 + x ^ 2) /
        ((lobeZero p) ^ 2 - x ^ 2) ^ 2) := by
    apply Summable.of_nonneg_of_le
      (fun p => by positivity)
      (fun p => ?_)
      (summable_inv_sq_lobeZero.mul_left (4 / (1 - x ^ 2) ^ 2))
    have ha := one_le_sq_lobeZero p
    have hgap : (lobeZero p) ^ 2 * (1 - x ^ 2) ≤
        (lobeZero p) ^ 2 - x ^ 2 := by nlinarith
    have hnum : 2 * ((lobeZero p) ^ 2 + x ^ 2) ≤
        4 * (lobeZero p) ^ 2 := by nlinarith
    have hsq : ((lobeZero p) ^ 2 * (1 - x ^ 2)) ^ 2 ≤
        ((lobeZero p) ^ 2 - x ^ 2) ^ 2 :=
      pow_le_pow_left₀
        (mul_nonneg (sq_nonneg _) (by linarith)) hgap 2
    have h1x : (1:ℝ) - x ^ 2 ≠ 0 := by nlinarith
    have ha0 : ((lobeZero p) ^ 2) ≠ 0 := by positivity
    rw [div_le_iff₀ (pow_pos (hden p) 2)]
    calc 2 * ((lobeZero p) ^ 2 + x ^ 2) ≤ 4 * (lobeZero p) ^ 2 := hnum
      _ = 4 / (1 - x ^ 2) ^ 2 * (1 / (lobeZero p) ^ 2) *
          ((lobeZero p) ^ 2 * (1 - x ^ 2)) ^ 2 := by
          field_simp
      _ ≤ 4 / (1 - x ^ 2) ^ 2 * (1 / (lobeZero p) ^ 2) *
          ((lobeZero p) ^ 2 - x ^ 2) ^ 2 := by
          apply mul_le_mul_of_nonneg_left hsq (by positivity)
  have hpos : 0 < ∑' p : ℕ × ℕ,
      2 * ((lobeZero p) ^ 2 + x ^ 2) /
        ((lobeZero p) ^ 2 - x ^ 2) ^ 2 := by
    apply hsummable.tsum_pos (fun p => by positivity) ((0, 0) : ℕ × ℕ)
    apply div_pos
    · nlinarith [one_le_sq_lobeZero ((0, 0) : ℕ × ℕ), sq_nonneg x]
    · exact pow_pos (hden ((0, 0) : ℕ × ℕ)) 2
  have hneg : (fun p : ℕ × ℕ => -(2 * ((lobeZero p) ^ 2 + x ^ 2)) /
      ((lobeZero p) ^ 2 - x ^ 2) ^ 2) =
      fun p => -(2 * ((lobeZero p) ^ 2 + x ^ 2) /
        ((lobeZero p) ^ 2 - x ^ 2) ^ 2) := by
    funext p
    rw [neg_div]
  rw [hneg, tsum_neg]
  linarith

/-- **Strict log-concavity on the central lobe** (`thm:one-peak`,
analytic half): the canonical log-series is strictly concave on
`(-1, 1)`. -/
theorem strictConcaveOn_central_log_series :
    StrictConcaveOn ℝ (Set.Ioo (-1:ℝ) 1)
      (fun z => ∑' p : ℕ × ℕ,
        Real.log (1 - z ^ 2 / (lobeZero p) ^ 2)) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ioo _ _)
  · intro x hx
    have hx' : |x| < 1 := abs_lt.mpr (Set.mem_Ioo.mp hx)
    exact (hasDerivAt_central_log_series
      hx').continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    have hxm := Set.mem_Ioo.mp hx
    have hx' : |x| < 1 := abs_lt.mpr hxm
    show deriv (deriv (fun z => ∑' p : ℕ × ℕ,
      Real.log (1 - z ^ 2 / (lobeZero p) ^ 2))) x < 0
    have hEv : deriv (fun z => ∑' p : ℕ × ℕ,
        Real.log (1 - z ^ 2 / (lobeZero p) ^ 2)) =ᶠ[𝓝 x]
        (fun z => ∑' p : ℕ × ℕ,
          -(2 * z) / ((lobeZero p) ^ 2 - z ^ 2)) := by
      have hnhds : Set.Ioo (-1:ℝ) 1 ∈ 𝓝 x :=
        Ioo_mem_nhds hxm.1 hxm.2
      filter_upwards [hnhds] with y hy
      exact (hasDerivAt_central_log_series
        (abs_lt.mpr (Set.mem_Ioo.mp hy))).deriv
    rw [hEv.deriv_eq, (hasDerivAt_central_log_deriv hx').deriv]
    exact central_log_second_deriv_neg hx'

end Fabius
