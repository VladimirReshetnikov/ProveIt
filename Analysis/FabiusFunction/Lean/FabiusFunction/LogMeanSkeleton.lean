import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The logarithmic-mean skeleton: bounded ends do not disturb the limit

The limit-theoretic skeleton of the audits' logarithmic-mean theorem
(`thm:logmean`): the logarithmic average over `[t₀, t]` decomposes into
`K = ⌊log₂ t⌋` complete-shell masses `β k → β∞`, one bounded terminal
partial-shell mass, and one bounded endpoint correction in the
denominator `log(t/t₀) = K·log 2 + O(1)`.  The analytic layer (RPF)
supplies `β k → β∞`; everything else is the following statement:

* `tendsto_sum_add_bdd_div` — if `β k → L` and `γ, δ` are bounded,
  then `((∑_{k<K} β k) + γ K)/(K + δ K) → L`.

Unlike the ordinary Cesàro mean, here the terminal block carries
weight `O(1/K)` — which is exactly why the logarithmic mean converges
*unrestrictedly* while the additive mean retains the dyadic-mantissa
profile of `CesaroProfileSkeleton`.  The audit's constant is then
`A₁^log = β∞ / log 2`, with `L = β∞` and the denominator measured in
units of `log 2`.
-/

set_option autoImplicit false

open Filter Finset

namespace Fabius

/-- Bounded numerators over `K` tend to zero: `γ K / K → 0`. -/
theorem tendsto_bdd_div_natCast {γ : ℕ → ℝ} {C : ℝ}
    (hγ : ∀ K, |γ K| ≤ C) :
    Tendsto (fun K : ℕ => γ K / K) atTop (nhds 0) := by
  refine squeeze_zero_norm (fun K => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat C)
  have hKinv : (0:ℝ) ≤ ((K : ℝ))⁻¹ := by positivity
  rw [Real.norm_eq_abs, abs_div, Nat.abs_cast, div_eq_mul_inv,
    div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hγ K) hKinv

/-- **The logarithmic-mean skeleton**: if the per-shell masses
converge, `β k → L`, and `γ, δ` are bounded (the terminal partial
shell and the endpoint correction), then
`((∑_{k<K} β k) + γ K)/((K : ℝ) + δ K) → L`. -/
theorem tendsto_sum_add_bdd_div {β : ℕ → ℝ} {L : ℝ}
    (hβ : Tendsto β atTop (nhds L)) {γ δ : ℕ → ℝ} {C : ℝ}
    (hγ : ∀ K, |γ K| ≤ C) (hδ : ∀ K, |δ K| ≤ C) :
    Tendsto (fun K : ℕ => ((∑ k ∈ range K, β k) + γ K) / ((K : ℝ) + δ K))
      atTop (nhds L) := by
  have hces : Tendsto (fun K : ℕ => (∑ k ∈ range K, β k) / K)
      atTop (nhds L) := by
    have h := hβ.cesaro
    refine h.congr fun K => ?_
    rw [inv_mul_eq_div]
  have hγ0 : Tendsto (fun K : ℕ => γ K / K) atTop (nhds 0) :=
    tendsto_bdd_div_natCast hγ
  have hδ0 : Tendsto (fun K : ℕ => δ K / K) atTop (nhds 0) :=
    tendsto_bdd_div_natCast hδ
  have hnum : Tendsto (fun K : ℕ => ((∑ k ∈ range K, β k) + γ K) / K)
      atTop (nhds L) := by
    have h := hces.add hγ0
    rw [add_zero] at h
    refine h.congr fun K => ?_
    rw [add_div]
  have hden : Tendsto (fun K : ℕ => ((K : ℝ) + δ K) / K)
      atTop (nhds 1) := by
    have h := (tendsto_const_nhds (x := (1:ℝ))).add hδ0
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with K hK
    have hKne : ((K : ℝ)) ≠ 0 := by
      have : (0:ℝ) < K := by exact_mod_cast hK
      exact ne_of_gt this
    rw [add_div, div_self hKne]
  have hq := hnum.div hden (by norm_num)
  rw [div_one] at hq
  refine hq.congr' ?_
  filter_upwards [eventually_ge_atTop (Nat.ceil C + 1)] with K hK
  have hKC : C < (K : ℝ) := by
    calc C ≤ Nat.ceil C := Nat.le_ceil C
      _ < (K : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hK
  have hKne : ((K : ℝ)) ≠ 0 := by
    have hC0 : 0 ≤ C := (abs_nonneg (δ 0)).trans (hδ 0)
    have : (0:ℝ) < K := lt_of_le_of_lt hC0 hKC
    exact ne_of_gt this
  have hdenne : ((K : ℝ) + δ K) ≠ 0 := by
    have h1 : -C ≤ δ K := neg_le_of_abs_le (hδ K)
    have : (0:ℝ) < (K : ℝ) + δ K := by linarith
    exact ne_of_gt this
  simp only [Pi.div_apply]
  field_simp

end Fabius
