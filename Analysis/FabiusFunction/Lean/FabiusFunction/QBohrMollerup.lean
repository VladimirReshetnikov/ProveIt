import FabiusFunction.QGammaLogConvex
import FabiusFunction.QBetaIntegral
import FabiusFunction.QBinomialTheoremInfinite
import FabiusFunction.QPochhammerInfiniteBounds
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The `q`-Bohr–Mollerup theorem

For `0 < q < 1`, `Γ_q` is the unique function `f : (0,∞) → (0,∞)` with `f(1) = 1`,
`f(x+1) = [x]_q f(x)` and `log f` convex.

The proof is Artin's: for `0 < x < 1` and `m ≥ 1`, the convexity of `log f` on the points
`m < m+1 < m+1+x < m+2` gives `[m]_q^x ≤ f(m+1+x)/f(m+1) ≤ [m+1]_q^x`; the functional
equation turns this into the two-sided bound

`[m]_q^x [m]_q! / ([x]_q ⋯ [x+m]_q) ≤ f(x) ≤ [m+1]_q^x [m]_q! / ([x]_q ⋯ [x+m]_q)`,

and both bounds tend to `Γ_q(x)` (`tendsto_qGamma_limit`, the `q`-analogue of Euler's limit
formula).  The functional equation then extends the identity from `(0,1]` to `(0,∞)`.

## Main declarations

* `funcEq_add_nat`, `funcEq_nat_succ`, `qGamma_add_nat`.
* `prod_qNumber_succ`, `prod_qNumber_add`: the products as `q`-Pochhammer symbols.
* `tendsto_qGamma_limit`: `Γ_q(x) = lim [m+1]_q^x [m]_q!/([x]_q ⋯ [x+m]_q)`.
* `qGamma_eq_of_logConvex`: the `q`-Bohr–Mollerup theorem.
-/

set_option autoImplicit false

open Filter Topology Set Finset

namespace Fabius

variable {q : ℝ}

/-- Iterating the functional equation: `f(x + k) = [x]_q [x+1]_q ⋯ [x+k-1]_q f(x)`. -/
theorem funcEq_add_nat {f : ℝ → ℝ} (hfe : ∀ x, 0 < x → f (x + 1) = qNumber q x * f x)
    {x : ℝ} (hx : 0 < x) (k : ℕ) :
    f (x + k) = (∏ j ∈ range k, qNumber q (x + j)) * f x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, show x + ((k + 1 : ℕ) : ℝ) = (x + k) + 1 by push_cast; ring,
      hfe _ (by positivity), ih]
    ring

/-- The values at the positive integers: `f(n+1) = [1]_q [2]_q ⋯ [n]_q`. -/
theorem funcEq_nat_succ {f : ℝ → ℝ} (h1 : f 1 = 1)
    (hfe : ∀ x, 0 < x → f (x + 1) = qNumber q x * f x) (n : ℕ) :
    f ((n : ℝ) + 1) = ∏ j ∈ range n, qNumber q ((j : ℝ) + 1) := by
  induction n with
  | zero => simpa using h1
  | succ n ih =>
    rw [prod_range_succ, ← ih, mul_comm, ← hfe _ (by positivity)]
    congr 1
    push_cast
    ring

/-- `Γ_q(x + k) = [x]_q ⋯ [x+k-1]_q Γ_q(x)`. -/
theorem qGamma_add_nat (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx : 0 < x) (k : ℕ) :
    qGamma q (x + k) = (∏ j ∈ range k, qNumber q (x + j)) * qGamma q x :=
  funcEq_add_nat (fun y hy => qGamma_add_one hq0 hq1 hy) hx k

/-- `[1]_q ⋯ [m]_q = (q;q)_m / (1-q)^m`. -/
theorem prod_qNumber_succ (m : ℕ) :
    ∏ j ∈ range m, qNumber q ((j : ℝ) + 1) = finiteQPochhammerIn q q m / (1 - q) ^ m := by
  unfold qNumber finiteQPochhammerIn
  rw [prod_div_distrib, prod_const, card_range]
  congr 1
  refine prod_congr rfl fun j _ => ?_
  rw [← Nat.cast_succ, Real.rpow_natCast, pow_succ']

/-- `[x]_q [x+1]_q ⋯ [x+m-1]_q = (q^x;q)_m / (1-q)^m`. -/
theorem prod_qNumber_add (hq0 : 0 < q) (x : ℝ) (m : ℕ) :
    ∏ j ∈ range m, qNumber q (x + j) = finiteQPochhammerIn (q ^ x) q m / (1 - q) ^ m := by
  unfold qNumber finiteQPochhammerIn
  rw [prod_div_distrib, prod_const, card_range]
  congr 1
  refine prod_congr rfl fun j _ => ?_
  rw [Real.rpow_add hq0, Real.rpow_natCast]

/-- **The `q`-analogue of Euler's limit formula**:
`[m+1]_q^x [m]_q! / ([x]_q [x+1]_q ⋯ [x+m]_q) → Γ_q(x)` as `m → ∞`, for `x > 0`. -/
theorem tendsto_qGamma_limit (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun m : ℕ => qNumber q ((m : ℝ) + 1) ^ x *
        (∏ j ∈ range m, qNumber q ((j : ℝ) + 1)) / ∏ j ∈ range (m + 1), qNumber q (x + j))
      atTop (𝓝 (qGamma q x)) := by
  have hq : ‖q‖ < 1 := norm_lt_one_of_pos_of_lt_one hq0 hq1
  have h1q : 0 < 1 - q := by linarith
  have hPx : 0 < qPochhammerInfIn (q ^ x) q := qPochhammerInfIn_rpow_pos hq0 hq1 hx
  have hseq : ∀ m : ℕ, qNumber q ((m : ℝ) + 1) ^ x *
      (∏ j ∈ range m, qNumber q ((j : ℝ) + 1)) / ∏ j ∈ range (m + 1), qNumber q (x + j) =
      (1 - q ^ (m + 1)) ^ x * (1 - q) ^ (1 - x) * finiteQPochhammerIn q q m /
        finiteQPochhammerIn (q ^ x) q (m + 1) := by
    intro m
    rw [prod_qNumber_succ, prod_qNumber_add hq0]
    unfold qNumber
    rw [← Nat.cast_succ, Real.rpow_natCast]
    have h1 : 0 < 1 - q ^ (m + 1) := sub_pos.mpr (pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero m))
    rw [Real.div_rpow h1.le h1q.le, Real.rpow_sub h1q, Real.rpow_one]
    have hx' : (1 - q) ^ x ≠ 0 := (Real.rpow_pos_of_pos h1q x).ne'
    have hm : (1 - q) ^ m ≠ 0 := pow_ne_zero _ h1q.ne'
    have hm1 : (1 - q) ^ (m + 1) ≠ 0 := pow_ne_zero _ h1q.ne'
    have hQ : finiteQPochhammerIn (q ^ x) q (m + 1) ≠ 0 :=
      finiteQPochhammerIn_ne_zero_of_qPochhammerInfIn_ne_zero (q ^ x) hq hPx.ne' (m + 1)
    field_simp
    ring
  simp_rw [hseq]
  have h1 : Tendsto (fun m : ℕ => (1 - q ^ (m + 1)) ^ x) atTop (𝓝 1) := by
    have h : Tendsto (fun m : ℕ => 1 - q ^ (m + 1)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub
        ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).comp (tendsto_add_atTop_nat 1))
    rw [sub_zero] at h
    simpa using h.rpow_const (Or.inl one_ne_zero)
  have h2 : Tendsto (fun m : ℕ => finiteQPochhammerIn q q m) atTop (𝓝 (qPochhammerInfIn q q)) :=
    tendsto_finiteQPochhammerIn_qPochhammerInfIn q hq
  have h3 : Tendsto (fun m : ℕ => finiteQPochhammerIn (q ^ x) q (m + 1)) atTop
      (𝓝 (qPochhammerInfIn (q ^ x) q)) :=
    (tendsto_finiteQPochhammerIn_qPochhammerInfIn (q ^ x) hq).comp (tendsto_add_atTop_nat 1)
  have h := ((h1.mul (tendsto_const_nhds (x := (1 - q) ^ (1 - x)))).mul h2).div h3 hPx.ne'
  have hlim : 1 * (1 - q) ^ (1 - x) * qPochhammerInfIn q q / qPochhammerInfIn (q ^ x) q =
      qGamma q x := by
    unfold qGamma
    ring
  rw [hlim] at h
  exact h

/-- **The `q`-Bohr–Mollerup theorem**: for `0 < q < 1`, a function `f` that is positive on
`(0,∞)`, has `f(1) = 1`, satisfies `f(x+1) = [x]_q f(x)`, and has `log f` convex on `(0,∞)`,
is `Γ_q` on `(0,∞)`. -/
theorem qGamma_eq_of_logConvex (hq0 : 0 < q) (hq1 : q < 1) {f : ℝ → ℝ}
    (hpos : ∀ x, 0 < x → 0 < f x) (h1 : f 1 = 1)
    (hfe : ∀ x, 0 < x → f (x + 1) = qNumber q x * f x)
    (hconv : ConvexOn ℝ (Ioi 0) (fun x => Real.log (f x))) :
    ∀ x, 0 < x → f x = qGamma q x := by
  have h1q : 0 < 1 - q := by linarith
  -- the case `0 < x < 1`
  have key : ∀ x, 0 < x → x < 1 → f x = qGamma q x := by
    intro x hx hx1
    have hFpos : ∀ m : ℕ, 0 < ∏ j ∈ range m, qNumber q ((j : ℝ) + 1) := fun m =>
      prod_pos fun j _ => qNumber_pos hq0 hq1 (by positivity)
    have hPpos : ∀ m : ℕ, 0 < ∏ j ∈ range m, qNumber q (x + j) := fun m =>
      prod_pos fun j _ => qNumber_pos hq0 hq1 (by positivity)
    have hfx : 0 < f x := hpos x hx
    -- the two-sided bound for `m ≥ 1`
    have hbound : ∀ m : ℕ, 1 ≤ m →
        qNumber q m ^ x * (∏ j ∈ range m, qNumber q ((j : ℝ) + 1)) /
            (∏ j ∈ range (m + 1), qNumber q (x + j)) ≤ f x ∧
        f x ≤ qNumber q ((m : ℝ) + 1) ^ x * (∏ j ∈ range m, qNumber q ((j : ℝ) + 1)) /
            (∏ j ∈ range (m + 1), qNumber q (x + j)) := by
      intro m hm
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      have ha : (m : ℝ) ∈ Ioi (0 : ℝ) := hm'
      have hb : (m : ℝ) + 1 ∈ Ioi (0 : ℝ) := by show (0 : ℝ) < m + 1; linarith
      have hc : (m : ℝ) + 1 + x ∈ Ioi (0 : ℝ) := by show (0 : ℝ) < m + 1 + x; linarith
      have hd : (m : ℝ) + 2 ∈ Ioi (0 : ℝ) := by show (0 : ℝ) < m + 2; linarith
      have hab : (m : ℝ) < m + 1 := by linarith
      have hbc : (m : ℝ) + 1 < m + 1 + x := by linarith
      have hcd : (m : ℝ) + 1 + x < m + 2 := by linarith
      have hlow : (Real.log (f ((m : ℝ) + 1)) - Real.log (f m)) / ((m : ℝ) + 1 - m) ≤
          (Real.log (f ((m : ℝ) + 1 + x)) - Real.log (f ((m : ℝ) + 1))) /
            ((m : ℝ) + 1 + x - (m + 1)) :=
        hconv.slope_mono_adjacent ha hc hab hbc
      have hup : (Real.log (f ((m : ℝ) + 1 + x)) - Real.log (f ((m : ℝ) + 1))) /
          ((m : ℝ) + 1 + x - (m + 1)) ≤
          (Real.log (f ((m : ℝ) + 2)) - Real.log (f ((m : ℝ) + 1))) / ((m : ℝ) + 2 - (m + 1)) :=
        hconv.secant_mono_aux2 hb hd hbc hcd
      have hfa : 0 < f m := hpos _ hm'
      have hfb0 : 0 < f ((m : ℝ) + 1) := hpos _ (by linarith)
      have hqm : 0 < qNumber q m := qNumber_pos hq0 hq1 hm'
      have hqm1 : 0 < qNumber q ((m : ℝ) + 1) := qNumber_pos hq0 hq1 (by linarith)
      have hfb : f ((m : ℝ) + 1) = qNumber q m * f m := hfe m hm'
      have hfd : f ((m : ℝ) + 2) = qNumber q ((m : ℝ) + 1) * f ((m : ℝ) + 1) := by
        have := hfe ((m : ℝ) + 1) (by linarith)
        rw [show (m : ℝ) + 1 + 1 = m + 2 by ring] at this
        exact this
      have hfc : f ((m : ℝ) + 1 + x) = (∏ j ∈ range (m + 1), qNumber q (x + j)) * f x := by
        rw [show (m : ℝ) + 1 + x = x + ((m + 1 : ℕ) : ℝ) by push_cast; ring]
        exact funcEq_add_nat hfe hx (m + 1)
      have hfF : f ((m : ℝ) + 1) = ∏ j ∈ range m, qNumber q ((j : ℝ) + 1) :=
        funcEq_nat_succ h1 hfe m
      rw [show (m : ℝ) + 1 - m = 1 by ring, show (m : ℝ) + 1 + x - (m + 1) = x by ring,
        div_one] at hlow
      rw [show (m : ℝ) + 1 + x - (m + 1) = x by ring, show (m : ℝ) + 2 - (m + 1) = 1 by ring,
        div_one] at hup
      have hlb : Real.log (f ((m : ℝ) + 1)) - Real.log (f m) = Real.log (qNumber q m) := by
        rw [hfb, Real.log_mul hqm.ne' hfa.ne']
        ring
      have hdb : Real.log (f ((m : ℝ) + 2)) - Real.log (f ((m : ℝ) + 1)) =
          Real.log (qNumber q ((m : ℝ) + 1)) := by
        rw [hfd, Real.log_mul hqm1.ne' hfb0.ne']
        ring
      have hR : 0 < (∏ j ∈ range (m + 1), qNumber q (x + j)) * f x /
          ∏ j ∈ range m, qNumber q ((j : ℝ) + 1) :=
        div_pos (mul_pos (hPpos _) hfx) (hFpos m)
      have hcb : Real.log (f ((m : ℝ) + 1 + x)) - Real.log (f ((m : ℝ) + 1)) =
          Real.log ((∏ j ∈ range (m + 1), qNumber q (x + j)) * f x /
            ∏ j ∈ range m, qNumber q ((j : ℝ) + 1)) := by
        rw [hfc, hfF, ← Real.log_div (mul_pos (hPpos _) hfx).ne' (hFpos m).ne']
      rw [hlb, hcb, le_div_iff₀ hx] at hlow
      rw [hcb, hdb, div_le_iff₀ hx] at hup
      have e1 : qNumber q m ^ x ≤ (∏ j ∈ range (m + 1), qNumber q (x + j)) * f x /
          ∏ j ∈ range m, qNumber q ((j : ℝ) + 1) := by
        rw [Real.rpow_def_of_pos hqm, ← Real.exp_log hR]
        exact Real.exp_le_exp.mpr hlow
      have e2 : (∏ j ∈ range (m + 1), qNumber q (x + j)) * f x /
          ∏ j ∈ range m, qNumber q ((j : ℝ) + 1) ≤ qNumber q ((m : ℝ) + 1) ^ x := by
        rw [Real.rpow_def_of_pos hqm1, ← Real.exp_log hR]
        exact Real.exp_le_exp.mpr hup
      rw [le_div_iff₀ (hFpos m)] at e1
      rw [div_le_iff₀ (hFpos m)] at e2
      constructor
      · rw [div_le_iff₀ (hPpos _)]
        linarith [e1, mul_comm (∏ j ∈ range (m + 1), qNumber q (x + j)) (f x)]
      · rw [le_div_iff₀ (hPpos _)]
        linarith [e2, mul_comm (∏ j ∈ range (m + 1), qNumber q (x + j)) (f x)]
    -- the limits of the two bounds
    have hup_lim := tendsto_qGamma_limit hq0 hq1 hx
    have hqnn : ∀ m : ℕ, 0 ≤ qNumber q m := fun m =>
      div_nonneg (sub_nonneg.mpr (Real.rpow_le_one hq0.le hq1.le (Nat.cast_nonneg m))) h1q.le
    have hratio : Tendsto (fun m : ℕ => (qNumber q m / qNumber q ((m : ℝ) + 1)) ^ x) atTop
        (𝓝 1) := by
      have hnum : Tendsto (fun m : ℕ => qNumber q m) atTop (𝓝 ((1 - 0) / (1 - q))) := by
        unfold qNumber
        simp_rw [Real.rpow_natCast]
        exact (tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1)).div_const _
      have hden : Tendsto (fun m : ℕ => qNumber q ((m : ℝ) + 1)) atTop (𝓝 ((1 - 0) / (1 - q))) := by
        unfold qNumber
        simp_rw [← Nat.cast_succ, Real.rpow_natCast]
        exact (tendsto_const_nhds.sub
          ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).comp (tendsto_add_atTop_nat 1))).div_const _
      have hne : (1 - 0) / (1 - q) ≠ 0 := by
        rw [sub_zero]
        exact (one_div_pos.mpr h1q).ne'
      have h := (hnum.div hden hne).rpow_const (Or.inr hx.le)
      rwa [div_self hne, Real.one_rpow] at h
    have hlow_lim : Tendsto (fun m : ℕ => qNumber q m ^ x *
        (∏ j ∈ range m, qNumber q ((j : ℝ) + 1)) / ∏ j ∈ range (m + 1), qNumber q (x + j))
        atTop (𝓝 (qGamma q x)) := by
      have heq : ∀ m : ℕ, qNumber q m ^ x *
          (∏ j ∈ range m, qNumber q ((j : ℝ) + 1)) / ∏ j ∈ range (m + 1), qNumber q (x + j) =
          (qNumber q m / qNumber q ((m : ℝ) + 1)) ^ x *
            (qNumber q ((m : ℝ) + 1) ^ x * (∏ j ∈ range m, qNumber q ((j : ℝ) + 1)) /
              ∏ j ∈ range (m + 1), qNumber q (x + j)) := by
        intro m
        have hqm1 : 0 < qNumber q ((m : ℝ) + 1) := qNumber_pos hq0 hq1 (by positivity)
        have hqm1x : qNumber q ((m : ℝ) + 1) ^ x ≠ 0 := (Real.rpow_pos_of_pos hqm1 x).ne'
        have hP0 : (∏ j ∈ range (m + 1), qNumber q (x + j)) ≠ 0 := (hPpos (m + 1)).ne'
        rw [Real.div_rpow (hqnn m) hqm1.le]
        field_simp
      simp_rw [heq]
      simpa using hratio.mul hup_lim
    have hconst : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (qGamma q x)) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_lim hup_lim ?_ ?_
      · filter_upwards [eventually_ge_atTop 1] with m hm
        exact (hbound m hm).1
      · filter_upwards [eventually_ge_atTop 1] with m hm
        exact (hbound m hm).2
    exact (tendsto_nhds_unique hconst tendsto_const_nhds).symm
  -- general `x > 0`: write `x = y + k` with `0 < y ≤ 1`
  intro x hx
  obtain ⟨k, y, hy0, hy1, rfl⟩ : ∃ (k : ℕ) (y : ℝ), 0 < y ∧ y ≤ 1 ∧ x = y + k := by
    have h2 : 1 ≤ ⌈x⌉₊ := Nat.ceil_pos.mpr hx
    refine ⟨⌈x⌉₊ - 1, x - ((⌈x⌉₊ - 1 : ℕ) : ℝ), ?_, ?_, by ring⟩
    · have := Nat.ceil_lt_add_one hx.le
      rw [Nat.cast_sub h2, Nat.cast_one]
      linarith
    · have := Nat.le_ceil x
      rw [Nat.cast_sub h2, Nat.cast_one]
      linarith
  have hy : f y = qGamma q y := by
    rcases hy1.lt_or_eq with hlt | heq
    · exact key y hy0 hlt
    · rw [heq, h1, qGamma_one hq0 hq1]
  rw [funcEq_add_nat hfe hy0 k, qGamma_add_nat hq0 hq1 hy0 k, hy]

end Fabius
