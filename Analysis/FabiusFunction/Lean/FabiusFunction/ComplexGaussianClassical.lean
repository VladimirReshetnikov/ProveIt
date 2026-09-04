import FabiusFunction.QBohrMollerup
import FabiusFunction.ClassicalPochhammerLimit
import FabiusFunction.ComplexGaussianBinomial
import FabiusFunction.QGammaLogDerivative
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The classical limit `q → 1⁻` of the two-argument Gaussian coefficient

For real `0 < q < 1` and real `α, β` the **two-argument Gaussian coefficient** is

`[α,β]_q = (q^{β+1};q)_∞ (q^{α-β+1};q)_∞ / ((q;q)_∞ (q^{α+1};q)_∞)`

(`gaussianBinomialRR`, the real avatar of the corpus object `gaussianBinomialCC`), and this
module proves that it converges to the classical quotient of Euler gamma values

`lim_{q→1⁻} [α,β]_q = Γ(α+1) / (Γ(β+1) Γ(α-β+1))`

whenever the three gamma arguments are positive.

The route is the one the source text sketches, but carried out in full.

* **The Artin bound is exported.**  For any `f` positive on `(0,∞)` with `f(1) = 1`,
  `f(x+1) = [x]_q f(x)` and `log f` convex, log-convexity applied to the four points
  `m < m+1 < m+1+x < m+2` gives, for `0 < x < 1` and `m ≥ 1`,

  `[m]_q^x [1]_q⋯[m]_q / ([x]_q⋯[x+m]_q) ≤ f(x) ≤ [m+1]_q^x [1]_q⋯[m]_q / ([x]_q⋯[x+m]_q)`.

  In `QBohrMollerup` this bound is an anonymous `have` inside the proof of
  `qGamma_eq_of_logConvex`; here it becomes the reusable `logConvex_two_sided_bound`, with the
  `Γ_q`-instance `qGamma_two_sided_bound`.

* **The `q`-numbers converge to their classical values.**  `[y]_q → y`, `[1]_q⋯[m]_q → m!` and
  `[x]_q⋯[x+m-1]_q → x(x+1)⋯(x+m-1)` as `q → 1⁻`; all three are instances of the classical
  Pochhammer limit `(q^x;q)_n/(1-q)^n → (x)_n` of `ClassicalPochhammerLimit`, restricted from
  `𝓝[≠] 1` to `𝓝[<] 1`.

* **Squeeze.**  The two outer bounds therefore converge, as `q → 1⁻`, to Euler's sequence
  `n^x n!/(x⋯(x+n))` and to its shifted companion `(n+1)^x n!/(x⋯(x+n))`, both of which tend to
  `Γ(x)` as `n → ∞`.  The order characterisation of limits (`tendsto_order`) turns this into
  `Γ_q(x) → Γ(x)` for `0 < x ≤ 1`, and the functional equations of `Γ_q` and `Γ` extend it to
  every `x > 0`.

* **The corollary.**  `[α,β]_q = Γ_q(α+1)/(Γ_q(β+1) Γ_q(α-β+1))` (all powers of `1-q` cancel),
  so three pointwise limits and continuity of division give the classical value; the limit
  denominator `Γ(β+1) Γ(α-β+1)` is nonzero because both factors are positive.

## Main declarations

* `logConvex_two_sided_bound`, `qGamma_two_sided_bound`: the two-sided Artin bound.
* `tendsto_qNumber_nhdsLT_one`, `tendsto_prod_qNumber_succ_nhdsLT_one`,
  `tendsto_prod_qNumber_add_nhdsLT_one`: the `q → 1⁻` limits of `q`-numbers.
* `tendsto_gammaSeq_shift`: `(n+1)^x n!/(x⋯(x+n)) → Γ(x)`.
* `tendsto_qGamma_nhdsLT_one`: **`Γ_q(x) → Γ(x)` as `q → 1⁻`, for every `x > 0`.**
* `gaussianBinomialRR`, `gaussianBinomialRR_eq_qGamma`.
* `tendsto_gaussianBinomialRR_nhdsLT_one`: **the classical generalized binomial limit.**
* `ofReal_gaussianBinomialRR`, `tendsto_gaussianBinomialCC_ofReal_nhdsLT_one`: the same limit
  for the complex object `gaussianBinomialCC` at real arguments.

## Scope relative to the source statement

The source corollary assumes `α > β > -1`.  That is strictly stronger than what the proof uses:
only the positivity of the three gamma arguments enters, so the hypotheses here are the three
independent conditions `0 < α + 1`, `0 < β + 1`, `0 < α - β + 1` (e.g. `α = -1/2`, `β = 1/5`
satisfies all three but not `α > β`).

The source cites a *locally uniform* `q`-gamma limit.  Local uniformity is **not** proved here,
and is not needed: the coefficient is a quotient of `Γ_q` at the three *fixed* points `α+1`,
`β+1`, `α-β+1`, so three pointwise limits suffice.  Accordingly `tendsto_qGamma_nhdsLT_one` is
the pointwise half only.  Nothing is claimed about complex `α, β` (the object `qGammaC` at a
genuinely complex argument), about `q → 1` along complex `q`, or about `q → 1⁺`.
-/

set_option autoImplicit false

open Filter Topology Set Finset

namespace Fabius

/-! ### Elementary preliminaries -/

/-- Iterating `Γ(y+1) = y Γ(y)`: `Γ(y + k) = y(y+1)⋯(y+k-1) Γ(y)` for `y > 0`. -/
theorem realGamma_add_nat {y : ℝ} (hy : 0 < y) (k : ℕ) :
    Real.Gamma (y + k) = (∏ j ∈ range k, (y + (j : ℝ))) * Real.Gamma y := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : (0 : ℝ) < y + k := by positivity
    rw [show y + ((k + 1 : ℕ) : ℝ) = (y + k) + 1 by push_cast; ring,
      Real.Gamma_add_one hpos.ne', ih, prod_range_succ]
    ring

/-- Euler's sequence, spelled out: `Γ_n(x) = n^x n! / (x(x+1)⋯(x+n))`.  This is a definitional
unfolding of `Real.GammaSeq`, named so that the two `Tendsto` statements below can be matched
against each other syntactically. -/
theorem realGammaSeq_eq (x : ℝ) (m : ℕ) :
    Real.GammaSeq x m =
      (m : ℝ) ^ x * (Nat.factorial m : ℝ) / ∏ j ∈ range (m + 1), (x + (j : ℝ)) :=
  rfl

/-- Points of `𝓝[<] 1` are eventually in `(0,1)`; this discharges the ubiquitous side
conditions `0 < q` and `q < 1`. -/
theorem eventually_pos_lt_one_nhdsLT_one : ∀ᶠ q : ℝ in 𝓝[<] (1 : ℝ), 0 < q ∧ q < 1 := by
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with q hq
  exact ⟨hq.1, hq.2⟩

/-! ### The `q → 1⁻` limits of `q`-numbers -/

/-- **`[y]_q → y` as `q → 1⁻`.**  This is the classical Pochhammer limit at length one. -/
theorem tendsto_qNumber_nhdsLT_one (y : ℝ) :
    Tendsto (fun q : ℝ => qNumber q y) (𝓝[<] (1 : ℝ)) (𝓝 y) := by
  have hval : (ascPochhammer ℝ 1).eval y = y := by
    rw [ascPochhammer_eval_eq_prod_range]
    simp
  have h := (tendsto_finiteQPochhammerIn_rpow_div_pow y 1).mono_left (nhdsLT_le_nhdsNE 1)
  rw [hval] at h
  refine h.congr fun q => ?_
  have hone : finiteQPochhammerIn (q ^ y) q 1 = 1 - q ^ y := by
    simp [finiteQPochhammerIn]
  rw [hone, pow_one, qNumber]

/-- **`[1]_q [2]_q ⋯ [m]_q → m!` as `q → 1⁻`.** -/
theorem tendsto_prod_qNumber_succ_nhdsLT_one (n : ℕ) :
    Tendsto (fun q : ℝ => ∏ j ∈ range n, qNumber q ((j : ℝ) + 1)) (𝓝[<] (1 : ℝ))
      (𝓝 (Nat.factorial n : ℝ)) := by
  have h := (tendsto_finiteQPochhammerIn_rpow_div_pow 1 n).mono_left (nhdsLT_le_nhdsNE 1)
  rw [ascPochhammer_eval_one] at h
  refine h.congr fun q => ?_
  rw [Real.rpow_one]
  exact (prod_qNumber_succ n).symm

/-- **`[x]_q [x+1]_q ⋯ [x+n-1]_q → x(x+1)⋯(x+n-1)` as `q → 1⁻`.** -/
theorem tendsto_prod_qNumber_add_nhdsLT_one (x : ℝ) (n : ℕ) :
    Tendsto (fun q : ℝ => ∏ j ∈ range n, qNumber q (x + j)) (𝓝[<] (1 : ℝ))
      (𝓝 (∏ j ∈ range n, (x + (j : ℝ)))) := by
  have h := (tendsto_finiteQPochhammerIn_rpow_div_pow x n).mono_left (nhdsLT_le_nhdsNE 1)
  rw [ascPochhammer_eval_eq_prod_range] at h
  refine h.congr' ?_
  filter_upwards [eventually_pos_lt_one_nhdsLT_one] with q hq
  exact (prod_qNumber_add hq.1 x n).symm

/-! ### The two-sided Artin bound -/

/-- **The two-sided Artin bound.**  If `f` is positive on `(0,∞)`, satisfies `f(1) = 1` and the
`q`-functional equation `f(x+1) = [x]_q f(x)`, and `log f` is convex on `(0,∞)`, then for
`0 < x < 1` and `m ≥ 1`

`[m]_q^x [1]_q⋯[m]_q / ([x]_q⋯[x+m]_q) ≤ f(x) ≤ [m+1]_q^x [1]_q⋯[m]_q / ([x]_q⋯[x+m]_q)`.

This is the bound that the proof of the `q`-Bohr–Mollerup theorem uses internally; it is stated
here separately because the classical limit `Γ_q → Γ` needs it as an input. -/
theorem logConvex_two_sided_bound {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {f : ℝ → ℝ}
    (hpos : ∀ x, 0 < x → 0 < f x) (h1 : f 1 = 1)
    (hfe : ∀ x, 0 < x → f (x + 1) = qNumber q x * f x)
    (hconv : ConvexOn ℝ (Ioi 0) (fun x => Real.log (f x)))
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) {m : ℕ} (hm : 1 ≤ m) :
    qNumber q m ^ x * (∏ j ∈ range m, qNumber q ((j : ℝ) + 1)) /
        (∏ j ∈ range (m + 1), qNumber q (x + j)) ≤ f x ∧
      f x ≤ qNumber q ((m : ℝ) + 1) ^ x * (∏ j ∈ range m, qNumber q ((j : ℝ) + 1)) /
        (∏ j ∈ range (m + 1), qNumber q (x + j)) := by
  have hFpos : ∀ n : ℕ, 0 < ∏ j ∈ range n, qNumber q ((j : ℝ) + 1) := fun n =>
    prod_pos fun j _ => qNumber_pos hq0 hq1 (by positivity)
  have hPpos : ∀ n : ℕ, 0 < ∏ j ∈ range n, qNumber q (x + j) := fun n =>
    prod_pos fun j _ => qNumber_pos hq0 hq1 (by positivity)
  have hfx : 0 < f x := hpos x hx
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

/-- **The two-sided Artin bound for `Γ_q`.**  For `0 < q < 1`, `0 < x < 1` and `m ≥ 1`,

`[m]_q^x [1]_q⋯[m]_q / ([x]_q⋯[x+m]_q) ≤ Γ_q(x) ≤ [m+1]_q^x [1]_q⋯[m]_q / ([x]_q⋯[x+m]_q)`. -/
theorem qGamma_two_sided_bound {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) {m : ℕ} (hm : 1 ≤ m) :
    qNumber q m ^ x * (∏ j ∈ range m, qNumber q ((j : ℝ) + 1)) /
        (∏ j ∈ range (m + 1), qNumber q (x + j)) ≤ qGamma q x ∧
      qGamma q x ≤ qNumber q ((m : ℝ) + 1) ^ x * (∏ j ∈ range m, qNumber q ((j : ℝ) + 1)) /
        (∏ j ∈ range (m + 1), qNumber q (x + j)) :=
  logConvex_two_sided_bound (f := qGamma q) hq0 hq1 (fun _ hy => qGamma_pos hq0 hq1 hy)
    (qGamma_one hq0 hq1) (fun _ hy => qGamma_add_one hq0 hq1 hy)
    (strictConvexOn_log_qGamma hq0 hq1).convexOn hx hx1 hm

/-! ### The classical limit of the `q`-gamma function -/

/-- The shifted Euler sequence `(m+1)^x m! / (x(x+1)⋯(x+m))` also converges to `Γ(x)`: it is
`(((m+1)/m)^x)` times Euler's own sequence, and the factor tends to `1`.  As with Mathlib's
`Real.GammaSeq_tendsto_Gamma`, no positivity of `x` is needed. -/
theorem tendsto_gammaSeq_shift (x : ℝ) :
    Tendsto (fun m : ℕ => ((m : ℝ) + 1) ^ x * (Nat.factorial m : ℝ) /
        ∏ j ∈ range (m + 1), (x + (j : ℝ))) atTop (𝓝 (Real.Gamma x)) := by
  have hratio : Tendsto (fun m : ℕ => ((m : ℝ) + 1) / (m : ℝ)) atTop (𝓝 1) := by
    have h : Tendsto (fun m : ℕ => 1 + 1 / (m : ℝ)) atTop (𝓝 ((1 : ℝ) + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    rw [add_div, div_self hmpos.ne']
  have hrpow : Tendsto (fun m : ℕ => (((m : ℝ) + 1) / (m : ℝ)) ^ x) atTop (𝓝 1) := by
    have h : Tendsto (fun m : ℕ => (((m : ℝ) + 1) / (m : ℝ)) ^ x) atTop (𝓝 ((1 : ℝ) ^ x)) :=
      hratio.rpow_const (Or.inl one_ne_zero)
    rwa [Real.one_rpow] at h
  have hmul := hrpow.mul (Real.GammaSeq_tendsto_Gamma x)
  rw [one_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hb1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have hmx : ((m : ℝ)) ^ x ≠ 0 := (Real.rpow_pos_of_pos hm0 x).ne'
  show (((m : ℝ) + 1) / (m : ℝ)) ^ x * Real.GammaSeq x m =
    ((m : ℝ) + 1) ^ x * (Nat.factorial m : ℝ) / ∏ j ∈ range (m + 1), (x + (j : ℝ))
  calc (((m : ℝ) + 1) / (m : ℝ)) ^ x * Real.GammaSeq x m
      = ((m : ℝ) + 1) ^ x / (m : ℝ) ^ x *
          ((m : ℝ) ^ x * (Nat.factorial m : ℝ) / ∏ j ∈ range (m + 1), (x + (j : ℝ))) := by
        rw [Real.div_rpow hb1 hm0.le, realGammaSeq_eq]
    _ = (m : ℝ) ^ x / (m : ℝ) ^ x *
          (((m : ℝ) + 1) ^ x * (Nat.factorial m : ℝ) / ∏ j ∈ range (m + 1), (x + (j : ℝ))) := by
        ring
    _ = ((m : ℝ) + 1) ^ x * (Nat.factorial m : ℝ) / ∏ j ∈ range (m + 1), (x + (j : ℝ)) := by
        rw [div_self hmx, one_mul]

/-- **`Γ_q(x) → Γ(x)` as `q → 1⁻`, for `0 < x ≤ 1`.**  Squeeze the Artin bound: for each fixed
`m ≥ 1` the two outer bounds converge, as `q → 1⁻`, to Euler's sequence and to its shift, and
both of those converge to `Γ(x)` as `m → ∞`. -/
theorem tendsto_qGamma_nhdsLT_one_of_le_one {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Tendsto (fun q : ℝ => qGamma q x) (𝓝[<] (1 : ℝ)) (𝓝 (Real.Gamma x)) := by
  rcases hx1.lt_or_eq with hlt | heq
  · rw [tendsto_order]
    refine ⟨?_, ?_⟩
    · -- lower bounds: pick `m` with `a < Γ_m(x)`, then `a < L_m(q) ≤ Γ_q(x)` eventually
      intro a ha
      obtain ⟨m, hm1, hma⟩ : ∃ m : ℕ, 1 ≤ m ∧ a < Real.GammaSeq x m := by
        obtain ⟨m, hm⟩ := (((Real.GammaSeq_tendsto_Gamma x).eventually
          (eventually_gt_nhds ha)).and (eventually_ge_atTop 1)).exists
        exact ⟨m, hm.2, hm.1⟩
      have hPpos : (0 : ℝ) < ∏ j ∈ range (m + 1), (x + (j : ℝ)) :=
        prod_pos fun j _ => by positivity
      have hnum : Tendsto (fun q : ℝ => qNumber q (m : ℝ) ^ x) (𝓝[<] (1 : ℝ))
          (𝓝 ((m : ℝ) ^ x)) :=
        (tendsto_qNumber_nhdsLT_one (m : ℝ)).rpow_const (Or.inr hx.le)
      have hL : Tendsto (fun q : ℝ => qNumber q m ^ x *
          (∏ j ∈ range m, qNumber q ((j : ℝ) + 1)) /
            (∏ j ∈ range (m + 1), qNumber q (x + j))) (𝓝[<] (1 : ℝ))
          (𝓝 (Real.GammaSeq x m)) := by
        rw [realGammaSeq_eq]
        have hdiv := (hnum.mul (tendsto_prod_qNumber_succ_nhdsLT_one m)).div
          (tendsto_prod_qNumber_add_nhdsLT_one x (m + 1)) hPpos.ne'
        exact hdiv
      filter_upwards [hL.eventually (eventually_gt_nhds hma),
        eventually_pos_lt_one_nhdsLT_one] with q hqL hq
      exact lt_of_lt_of_le hqL (qGamma_two_sided_bound hq.1 hq.2 hx hlt hm1).1
    · -- upper bounds: pick `m` with the shifted sequence below `a`
      intro a ha
      obtain ⟨m, hm1, hma⟩ : ∃ m : ℕ, 1 ≤ m ∧
          ((m : ℝ) + 1) ^ x * (Nat.factorial m : ℝ) /
            (∏ j ∈ range (m + 1), (x + (j : ℝ))) < a := by
        obtain ⟨m, hm⟩ := (((tendsto_gammaSeq_shift x).eventually
          (eventually_lt_nhds ha)).and (eventually_ge_atTop 1)).exists
        exact ⟨m, hm.2, hm.1⟩
      have hPpos : (0 : ℝ) < ∏ j ∈ range (m + 1), (x + (j : ℝ)) :=
        prod_pos fun j _ => by positivity
      have hnum : Tendsto (fun q : ℝ => qNumber q ((m : ℝ) + 1) ^ x) (𝓝[<] (1 : ℝ))
          (𝓝 (((m : ℝ) + 1) ^ x)) :=
        (tendsto_qNumber_nhdsLT_one ((m : ℝ) + 1)).rpow_const (Or.inr hx.le)
      have hU : Tendsto (fun q : ℝ => qNumber q ((m : ℝ) + 1) ^ x *
          (∏ j ∈ range m, qNumber q ((j : ℝ) + 1)) /
            (∏ j ∈ range (m + 1), qNumber q (x + j))) (𝓝[<] (1 : ℝ))
          (𝓝 (((m : ℝ) + 1) ^ x * (Nat.factorial m : ℝ) /
            (∏ j ∈ range (m + 1), (x + (j : ℝ))))) := by
        have hdiv := (hnum.mul (tendsto_prod_qNumber_succ_nhdsLT_one m)).div
          (tendsto_prod_qNumber_add_nhdsLT_one x (m + 1)) hPpos.ne'
        exact hdiv
      filter_upwards [hU.eventually (eventually_lt_nhds hma),
        eventually_pos_lt_one_nhdsLT_one] with q hqU hq
      exact lt_of_le_of_lt (qGamma_two_sided_bound hq.1 hq.2 hx hlt hm1).2 hqU
  · rw [heq, Real.Gamma_one]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_pos_lt_one_nhdsLT_one] with q hq
    exact (qGamma_one hq.1 hq.2).symm

/-- **The classical limit of the `q`-gamma function**: `Γ_q(x) → Γ(x)` as `q → 1⁻`, for every
`x > 0`.  Only the pointwise statement is proved; local uniformity on `(0,∞)` is not covered. -/
theorem tendsto_qGamma_nhdsLT_one {x : ℝ} (hx : 0 < x) :
    Tendsto (fun q : ℝ => qGamma q x) (𝓝[<] (1 : ℝ)) (𝓝 (Real.Gamma x)) := by
  obtain ⟨k, y, hy0, hy1, rfl⟩ : ∃ (k : ℕ) (y : ℝ), 0 < y ∧ y ≤ 1 ∧ x = y + k := by
    have h2 : 1 ≤ ⌈x⌉₊ := Nat.ceil_pos.mpr hx
    refine ⟨⌈x⌉₊ - 1, x - ((⌈x⌉₊ - 1 : ℕ) : ℝ), ?_, ?_, by ring⟩
    · have := Nat.ceil_lt_add_one hx.le
      rw [Nat.cast_sub h2, Nat.cast_one]
      linarith
    · have := Nat.le_ceil x
      rw [Nat.cast_sub h2, Nat.cast_one]
      linarith
  have hlim : Tendsto (fun q : ℝ => (∏ j ∈ range k, qNumber q (y + j)) * qGamma q y)
      (𝓝[<] (1 : ℝ)) (𝓝 (Real.Gamma (y + k))) := by
    rw [realGamma_add_nat hy0 k]
    exact (tendsto_prod_qNumber_add_nhdsLT_one y k).mul
      (tendsto_qGamma_nhdsLT_one_of_le_one hy0 hy1)
  refine hlim.congr' ?_
  filter_upwards [eventually_pos_lt_one_nhdsLT_one] with q hq
  exact (qGamma_add_nat hq.1 hq.2 hy0 k).symm

/-! ### The generalized Gaussian coefficient with two real arguments -/

/-- **The Gaussian coefficient with two real arguments**
`[α,β]_q = (q^{β+1};q)_∞ (q^{α-β+1};q)_∞ / ((q;q)_∞ (q^{α+1};q)_∞)`, the real avatar of
`gaussianBinomialCC`. -/
noncomputable def gaussianBinomialRR (q α β : ℝ) : ℝ :=
  qPochhammerInfIn (q ^ (β + 1)) q * qPochhammerInfIn (q ^ (α - β + 1)) q /
    (qPochhammerInfIn q q * qPochhammerInfIn (q ^ (α + 1)) q)

/-- **Gamma representation** `[α,β]_q = Γ_q(α+1)/(Γ_q(β+1) Γ_q(α-β+1))`: all powers of `1-q`
cancel, because `(1-q)^{-β} (1-q)^{β-α} = (1-q)^{-α}`. -/
theorem gaussianBinomialRR_eq_qGamma {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {α β : ℝ}
    (hα : 0 < α + 1) (hβ : 0 < β + 1) (hαβ : 0 < α - β + 1) :
    gaussianBinomialRR q α β =
      qGamma q (α + 1) / (qGamma q (β + 1) * qGamma q (α - β + 1)) := by
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hP : qPochhammerInfIn q q ≠ 0 := (qPochhammerInfIn_self_pos hq0 hq1).ne'
  have hA : qPochhammerInfIn (q ^ (α + 1)) q ≠ 0 := (qPochhammerInfIn_rpow_pos hq0 hq1 hα).ne'
  have hB : qPochhammerInfIn (q ^ (β + 1)) q ≠ 0 := (qPochhammerInfIn_rpow_pos hq0 hq1 hβ).ne'
  have hC : qPochhammerInfIn (q ^ (α - β + 1)) q ≠ 0 :=
    (qPochhammerInfIn_rpow_pos hq0 hq1 hαβ).ne'
  have hRa : (1 - q) ^ α ≠ 0 := (Real.rpow_pos_of_pos h1q α).ne'
  have hRb : (1 - q) ^ β ≠ 0 := (Real.rpow_pos_of_pos h1q β).ne'
  have hEa : (1 - q) ^ (1 - (α + 1)) = ((1 - q) ^ α)⁻¹ := by
    rw [show 1 - (α + 1) = -α by ring, Real.rpow_neg h1q.le]
  have hEb : (1 - q) ^ (1 - (β + 1)) = ((1 - q) ^ β)⁻¹ := by
    rw [show 1 - (β + 1) = -β by ring, Real.rpow_neg h1q.le]
  have hEc : (1 - q) ^ (1 - (α - β + 1)) = (1 - q) ^ β * ((1 - q) ^ α)⁻¹ := by
    rw [show 1 - (α - β + 1) = β + -α by ring, Real.rpow_add h1q, Real.rpow_neg h1q.le]
  unfold gaussianBinomialRR qGamma
  rw [hEa, hEb, hEc]
  field_simp
  all_goals ring

/-- **The classical generalized binomial limit.**  If the three gamma arguments are positive,

`lim_{q→1⁻} [α,β]_q = Γ(α+1) / (Γ(β+1) Γ(α-β+1))`.

The hypotheses are weaker than `α > β > -1`: only positivity of `α+1`, `β+1` and `α-β+1` is
used, and the limit denominator is nonzero because both gamma factors are positive. -/
theorem tendsto_gaussianBinomialRR_nhdsLT_one {α β : ℝ}
    (hα : 0 < α + 1) (hβ : 0 < β + 1) (hαβ : 0 < α - β + 1) :
    Tendsto (fun q : ℝ => gaussianBinomialRR q α β) (𝓝[<] (1 : ℝ))
      (𝓝 (Real.Gamma (α + 1) / (Real.Gamma (β + 1) * Real.Gamma (α - β + 1)))) := by
  have hne : Real.Gamma (β + 1) * Real.Gamma (α - β + 1) ≠ 0 :=
    (mul_pos (Real.Gamma_pos_of_pos hβ) (Real.Gamma_pos_of_pos hαβ)).ne'
  have h : Tendsto
      (fun q : ℝ => qGamma q (α + 1) / (qGamma q (β + 1) * qGamma q (α - β + 1)))
      (𝓝[<] (1 : ℝ))
      (𝓝 (Real.Gamma (α + 1) / (Real.Gamma (β + 1) * Real.Gamma (α - β + 1)))) := by
    have hdiv := (tendsto_qGamma_nhdsLT_one hα).div
      ((tendsto_qGamma_nhdsLT_one hβ).mul (tendsto_qGamma_nhdsLT_one hαβ)) hne
    exact hdiv
  refine h.congr' ?_
  filter_upwards [eventually_pos_lt_one_nhdsLT_one] with q hq
  exact (gaussianBinomialRR_eq_qGamma hq.1 hq.2 hα hβ hαβ).symm

/-! ### Transport to the complex two-argument coefficient -/

/-- At real arguments, `gaussianBinomialCC` is the real coefficient `gaussianBinomialRR`. -/
theorem ofReal_gaussianBinomialRR {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (α β : ℝ) :
    ((gaussianBinomialRR q α β : ℝ) : ℂ) = gaussianBinomialCC q (α : ℂ) (β : ℂ) := by
  have hq : ‖q‖ < 1 := norm_lt_one_of_pos_of_lt_one hq0 hq1
  have hcb : ((β + 1 : ℝ) : ℂ) = (β : ℂ) + 1 := by
    rw [Complex.ofReal_add, Complex.ofReal_one]
  have hca : ((α + 1 : ℝ) : ℂ) = (α : ℂ) + 1 := by
    rw [Complex.ofReal_add, Complex.ofReal_one]
  have hcab : ((α - β + 1 : ℝ) : ℂ) = (α : ℂ) - (β : ℂ) + 1 := by
    rw [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one]
  have e1 : ((q ^ (β + 1) : ℝ) : ℂ) = (q : ℂ) ^ ((β : ℂ) + 1) := by
    rw [Complex.ofReal_cpow hq0.le, hcb]
  have e2 : ((q ^ (α - β + 1) : ℝ) : ℂ) = (q : ℂ) ^ ((α : ℂ) - (β : ℂ) + 1) := by
    rw [Complex.ofReal_cpow hq0.le, hcab]
  have e3 : ((q ^ (α + 1) : ℝ) : ℂ) = (q : ℂ) ^ ((α : ℂ) + 1) := by
    rw [Complex.ofReal_cpow hq0.le, hca]
  unfold gaussianBinomialRR gaussianBinomialCC
  simp only [Complex.ofReal_div, Complex.ofReal_mul, ofReal_qPochhammerInfIn hq]
  rw [e1, e2, e3]

/-- **The classical generalized binomial limit for the complex coefficient at real arguments.**
For `0 < α + 1`, `0 < β + 1`, `0 < α - β + 1`,

`lim_{q→1⁻} [α,β]_q = Γ(α+1) / (Γ(β+1) Γ(α-β+1))` in `ℂ`. -/
theorem tendsto_gaussianBinomialCC_ofReal_nhdsLT_one {α β : ℝ}
    (hα : 0 < α + 1) (hβ : 0 < β + 1) (hαβ : 0 < α - β + 1) :
    Tendsto (fun q : ℝ => gaussianBinomialCC q (α : ℂ) (β : ℂ)) (𝓝[<] (1 : ℝ))
      (𝓝 ((Real.Gamma (α + 1) / (Real.Gamma (β + 1) * Real.Gamma (α - β + 1)) : ℝ) : ℂ)) := by
  have h := (Complex.continuous_ofReal.tendsto
      (Real.Gamma (α + 1) / (Real.Gamma (β + 1) * Real.Gamma (α - β + 1)))).comp
    (tendsto_gaussianBinomialRR_nhdsLT_one hα hβ hαβ)
  refine h.congr' ?_
  filter_upwards [eventually_pos_lt_one_nhdsLT_one] with q hq
  show ((gaussianBinomialRR q α β : ℝ) : ℂ) = gaussianBinomialCC q (α : ℂ) (β : ℂ)
  exact ofReal_gaussianBinomialRR hq.1 hq.2 α β

end Fabius
