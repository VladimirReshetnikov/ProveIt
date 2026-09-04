import FabiusFunction.JacobiTripleProduct

/-!
# Uniform convergence of the finite triple product on annuli

For `‖q‖ < 1` and `0 < r ≤ R`, the finite triple products `(z;q)_N (q/z;q)_N`, equivalently
the finite Laurent sums `∑_{k=-N}^{N} (-1)^k q^{e(k)} [2N, N+k]_q z^k`, converge to
`(z;q)_∞ (q/z;q)_∞` uniformly on the closed annulus `r ≤ ‖z‖ ≤ R`
(`tendstoUniformlyOn_finite_triple_product`, cor:jtp-from-finite).

The error is bounded, uniformly in `z`, by
`ε_N = ∑_k ‖q‖^{e(k)} ‖[2N,N+k]_q - (q;q)_∞⁻¹‖ (ρ^k + ρ^{-k})` with `ρ = max R r⁻¹`, and
`ε_N → 0` by dominated convergence (Tannery), since the Gaussian coefficients are bounded by
the Gaussian majorant and tend to `(q;q)_∞⁻¹`.
-/

set_option autoImplicit false

open Filter Topology Finset

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

omit [CompleteSpace 𝕜] in
/-- On the annulus `r ≤ ‖z‖ ≤ R`, `‖z‖^k ≤ ρ^k + ρ^{-k}` for `ρ = max R r⁻¹`. -/
theorem norm_zpow_le_of_mem_annulus {z : 𝕜} {r R : ℝ} (hr : 0 < r) (hz : r ≤ ‖z‖ ∧ ‖z‖ ≤ R)
    (k : ℤ) : ‖z‖ ^ k ≤ (max R r⁻¹) ^ k + (max R r⁻¹) ^ (-k) := by
  have hρ : 0 < max R r⁻¹ := lt_of_lt_of_le (inv_pos.mpr hr) (le_max_right _ _)
  rcases k with n | n
  · simp only [Int.ofNat_eq_natCast, zpow_natCast, zpow_neg]
    calc ‖z‖ ^ n ≤ (max R r⁻¹) ^ n :=
          pow_le_pow_left₀ (norm_nonneg z) (hz.2.trans (le_max_left _ _)) n
      _ ≤ (max R r⁻¹) ^ n + ((max R r⁻¹) ^ n)⁻¹ := le_add_of_nonneg_right (by positivity)
  · rw [zpow_negSucc, zpow_neg, zpow_negSucc, inv_inv]
    have h1 : (‖z‖ ^ (n + 1))⁻¹ ≤ (r ^ (n + 1))⁻¹ :=
      inv_anti₀ (pow_pos hr _) (pow_le_pow_left₀ hr.le hz.1 _)
    have h2 : (r ^ (n + 1))⁻¹ ≤ (max R r⁻¹) ^ (n + 1) := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (inv_nonneg.mpr hr.le) (le_max_right _ _) _
    calc (‖z‖ ^ (n + 1))⁻¹ ≤ (max R r⁻¹) ^ (n + 1) := h1.trans h2
      _ ≤ ((max R r⁻¹) ^ (n + 1))⁻¹ + (max R r⁻¹) ^ (n + 1) :=
          le_add_of_nonneg_left (by positivity)

/-- **Uniform convergence of the finite triple product on annuli** (cor:jtp-from-finite):
for `0 < r`, `(z;q)_N (q/z;q)_N → (z;q)_∞ (q/z;q)_∞` uniformly on `r ≤ ‖z‖ ≤ R`. -/
theorem tendstoUniformlyOn_finite_triple_product {q : 𝕜} (hq : ‖q‖ < 1) {r R : ℝ} (hr : 0 < r) :
    TendstoUniformlyOn
      (fun (N : ℕ) (z : 𝕜) => finiteQPochhammerIn z q N * finiteQPochhammerIn (q / z) q N)
      (fun z => qPochhammerInfIn z q * qPochhammerInfIn (q / z) q) atTop
      {z : 𝕜 | r ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
  have hI : qPochhammerInfIn q q ≠ 0 := qPochhammerInfIn_self_ne_zero hq
  set ρ : ℝ := max R r⁻¹ with hρdef
  have hρ : 0 < ρ := lt_of_lt_of_le (inv_pos.mpr hr) (le_max_right _ _)
  set L : 𝕜 := (qPochhammerInfIn q q)⁻¹ with hL
  set M : ℝ := gaussianMajorant q + ‖L‖ with hMdef
  -- the uniform error bound `ε_N = ∑_k d N k`
  set d : ℕ → ℤ → ℝ := fun N k =>
    ‖q‖ ^ thetaExponent k * ‖gaussianBinomialInt q (2 * N) ((N : ℤ) + k) - L‖ * (ρ ^ k + ρ ^ (-k))
    with hd
  have hbound_sum : Summable fun k : ℤ => M * (‖q‖ ^ thetaExponent k * (ρ ^ k + ρ ^ (-k))) := by
    have h1 := summable_pow_thetaExponent_mul_zpow (norm_nonneg q) hq hρ
    have h2 := summable_pow_thetaExponent_mul_zpow (norm_nonneg q) hq (inv_pos.mpr hρ)
    refine ((h1.add h2).mul_left M).congr fun k => ?_
    rw [inv_zpow']
    ring
  have hdnn : ∀ N k, 0 ≤ d N k := fun N k => by simp only [hd]; positivity
  have hdb : ∀ N k, ‖d N k‖ ≤ M * (‖q‖ ^ thetaExponent k * (ρ ^ k + ρ ^ (-k))) := by
    intro N k
    rw [Real.norm_eq_abs, abs_of_nonneg (hdnn N k)]
    simp only [hd]
    have h1 : ‖gaussianBinomialInt q (2 * N) ((N : ℤ) + k) - L‖ ≤ M :=
      (norm_sub_le _ _).trans (add_le_add (norm_gaussianBinomialInt_le hq _ _) le_rfl)
    calc ‖q‖ ^ thetaExponent k * ‖gaussianBinomialInt q (2 * N) ((N : ℤ) + k) - L‖ *
          (ρ ^ k + ρ ^ (-k))
        ≤ ‖q‖ ^ thetaExponent k * M * (ρ ^ k + ρ ^ (-k)) := by gcongr
      _ = M * (‖q‖ ^ thetaExponent k * (ρ ^ k + ρ ^ (-k))) := by ring
  have hdpt : ∀ k, Tendsto (fun N => d N k) atTop (𝓝 0) := by
    intro k
    have h1 := tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_gaussianBinomialInt_central hq k)
    have h2 := (h1.const_mul (‖q‖ ^ thetaExponent k)).mul_const (ρ ^ k + ρ ^ (-k))
    simpa [hd] using h2
  have hdsum : ∀ N, Summable (d N) := fun N =>
    Summable.of_norm_bounded hbound_sum (hdb N)
  have hεN : Tendsto (fun N => ∑' k, d N k) atTop (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence hbound_sum hdpt (Eventually.of_forall hdb)
    simpa using this
  -- the pointwise bound `dist (f z) (F N z) ≤ ε_N` on the annulus
  have hpt : ∀ N, ∀ z ∈ {z : 𝕜 | r ≤ ‖z‖ ∧ ‖z‖ ≤ R},
      dist (qPochhammerInfIn z q * qPochhammerInfIn (q / z) q)
        (finiteQPochhammerIn z q N * finiteQPochhammerIn (q / z) q N) ≤ ∑' k, d N k := by
    intro N z hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hr hz.1)
    -- the finite product as a bilateral sum
    have hF : HasSum (fun k : ℤ => (-1 : 𝕜) ^ k * q ^ thetaExponent k *
        gaussianBinomialInt q (2 * N) ((N : ℤ) + k) * z ^ k)
        (finiteQPochhammerIn z q N * finiteQPochhammerIn (q / z) q N) := by
      rw [finite_triple_product q hz0 N]
      refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
      rcases hk with hk | hk
      · rw [gaussianBinomialInt_eq_zero_of_neg q (2 * N) (by omega)]
        ring
      · rw [gaussianBinomialInt_eq_zero_of_lt q (2 * N) (by omega)]
        ring
    -- the infinite product as a bilateral sum
    have hf : HasSum (fun k : ℤ => (-1 : 𝕜) ^ k * q ^ thetaExponent k * L * z ^ k)
        (qPochhammerInfIn z q * qPochhammerInfIn (q / z) q) := by
      have h := (hasSum_jacobi_triple_product hq hz0).div_const (qPochhammerInfIn q q)
      rw [mul_div_cancel_right₀ _ hI] at h
      refine h.congr_fun fun k => ?_
      rw [hL, div_eq_mul_inv]
      ring
    have hdiff : HasSum (fun k : ℤ => (-1 : 𝕜) ^ k * q ^ thetaExponent k *
        (gaussianBinomialInt q (2 * N) ((N : ℤ) + k) - L) * z ^ k)
        (finiteQPochhammerIn z q N * finiteQPochhammerIn (q / z) q N -
          qPochhammerInfIn z q * qPochhammerInfIn (q / z) q) := by
      refine (hF.sub hf).congr_fun fun k => ?_
      ring
    have hterm : ∀ k : ℤ, ‖(-1 : 𝕜) ^ k * q ^ thetaExponent k *
        (gaussianBinomialInt q (2 * N) ((N : ℤ) + k) - L) * z ^ k‖ ≤ d N k := by
      intro k
      rw [norm_mul, norm_mul, norm_mul, norm_zpow, norm_zpow, norm_neg, norm_one, one_zpow, one_mul,
        norm_pow]
      simp only [hd]
      exact mul_le_mul_of_nonneg_left (norm_zpow_le_of_mem_annulus hr hz k) (by positivity)
    have hsn : Summable fun k : ℤ => ‖(-1 : 𝕜) ^ k * q ^ thetaExponent k *
        (gaussianBinomialInt q (2 * N) ((N : ℤ) + k) - L) * z ^ k‖ :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) hterm (hdsum N)
    rw [dist_eq_norm, norm_sub_rev, ← hdiff.tsum_eq]
    exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum hterm (hdsum N))
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
  filter_upwards [(tendsto_order.1 hεN).2 ε hε] with N hN
  intro z hz
  exact lt_of_le_of_lt (hpt N z hz) hN

/-- The finite Laurent sums of the triple product converge uniformly on annuli as well. -/
theorem tendstoUniformlyOn_finite_triple_product_sum {q : 𝕜} (hq : ‖q‖ < 1) {r R : ℝ}
    (hr : 0 < r) :
    TendstoUniformlyOn
      (fun (N : ℕ) (z : 𝕜) => ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        (-1 : 𝕜) ^ k * q ^ thetaExponent k * gaussianBinomialInt q (2 * N) ((N : ℤ) + k) * z ^ k)
      (fun z => qPochhammerInfIn z q * qPochhammerInfIn (q / z) q) atTop
      {z : 𝕜 | r ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
  refine (tendstoUniformlyOn_finite_triple_product hq (R := R) hr).congr ?_
  filter_upwards with N z hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hr hz.1)
  exact finite_triple_product q hz0 N

end Fabius
