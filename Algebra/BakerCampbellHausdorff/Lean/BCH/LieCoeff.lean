/-
# Every homogeneous BCH component lies in every closed Lie subalgebra

This file strengthens `BCH.LieClosed` (Proposition 8.1 of the accompanying
article, `docs/combined`) from the sum of the BCH series to its homogeneous
components: for a closed Lie subalgebra `𝔤` of a real or complex unital Banach
algebra and all `X, Y ∈ 𝔤` (no smallness assumption),

  `Zₙ(X, Y) ∈ 𝔤` for every `n`   (`bchHom_mem`).

This is the analytic form of the statement that the `Zₙ` are Lie polynomials.

## Method

For scalars `t` with `‖t‖ (‖X‖ + ‖Y‖)` small, `∑ₙ tⁿ Zₙ(X, Y) = log(e^{tX} e^{tY})`
lies in `𝔤` by Proposition 8.1 and homogeneity. A general lemma
(`mem_of_tsum_smul_mem`) extracts the coefficients: if `∑ₙ tⁿ cₙ ∈ 𝔤` for all
small `t ≠ 0`, with `∑ₙ rⁿ ‖cₙ‖ < ∞`, then every `cₙ` lies in the closed
subspace `𝔤`, by induction on `n`: `t⁻ⁿ (∑ₘ tᵐ cₘ - ∑_{i<n} tⁱ cᵢ) = cₙ + t T(t)`
lies in `𝔤` and tends to `cₙ` as `t → 0`.
-/
import BCH.LieClosed

open NormedSpace Filter Topology

namespace BCH

section Coefficients

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

omit [CompleteSpace 𝔸] in
lemma summable_pow_smul_of_norm_le {c : ℕ → 𝔸} {r : ℝ} (hsum : Summable fun n => r ^ n * ‖c n‖)
    {t : 𝕂} (ht : ‖t‖ ≤ r) : Summable fun n => ‖t ^ n • c n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hsum
  rw [norm_smul, norm_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ht n) (norm_nonneg _)

/-- **Coefficient extraction**: if `∑ₙ tⁿ cₙ ∈ 𝔤` for all `t` with `0 < ‖t‖ < r`, where
`∑ₙ rⁿ ‖cₙ‖ < ∞`, then every coefficient `cₙ` lies in the closed subspace `𝔤`. -/
theorem mem_of_tsum_smul_mem {𝔤 : Submodule 𝕂 𝔸} (hclosed : IsClosed (𝔤 : Set 𝔸))
    {c : ℕ → 𝔸} {r : ℝ} (hr : 0 < r) (hsum : Summable fun n => r ^ n * ‖c n‖)
    (hf : ∀ t : 𝕂, 0 < ‖t‖ → ‖t‖ < r → ∑' n, t ^ n • c n ∈ 𝔤) :
    ∀ n, c n ∈ 𝔤 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    -- the tail series `T(t) = ∑ₘ tᵐ c_{m+n+1}` and its bound on `‖t‖ ≤ r/2`
    have hshift : Summable fun m => r ^ (m + (n + 1)) * ‖c (m + (n + 1))‖ :=
      (summable_nat_add_iff (n + 1) (f := fun n => r ^ n * ‖c n‖)).2 hsum
    set C : ℝ := (r ^ (n + 1))⁻¹ * ∑' m, r ^ (m + (n + 1)) * ‖c (m + (n + 1))‖ with hC
    have hC0 : 0 ≤ C := mul_nonneg (by positivity) (tsum_nonneg fun m => by positivity)
    have hTbound : ∀ t : 𝕂, ‖t‖ ≤ r → ‖∑' m, t ^ m • c (m + (n + 1))‖ ≤ C := by
      intro t ht
      have hr' : r ^ (n + 1) ≠ 0 := by positivity
      have hterm : ∀ m, ‖t ^ m • c (m + (n + 1))‖ ≤
          (r ^ (n + 1))⁻¹ * (r ^ (m + (n + 1)) * ‖c (m + (n + 1))‖) := by
        intro m
        have hrhs : (r ^ (n + 1))⁻¹ * (r ^ (m + (n + 1)) * ‖c (m + (n + 1))‖) =
            r ^ m * ‖c (m + (n + 1))‖ := by
          rw [pow_add r m (n + 1), mul_comm (r ^ m) (r ^ (n + 1)), mul_assoc (r ^ (n + 1)),
            inv_mul_cancel_left₀ hr']
        rw [norm_smul, norm_pow, hrhs]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ht m) (norm_nonneg _)
      rw [hC]
      exact tsum_of_norm_bounded (hshift.hasSum.mul_left _) hterm
    -- the identity `t⁻ⁿ (S(t) - ∑_{i<n} tⁱ cᵢ) = cₙ + t T(t)`
    have hsplit : ∀ t : 𝕂, ‖t‖ ≤ r →
        (∑' m, t ^ m • c m) = (∑ i ∈ Finset.range n, t ^ i • c i) +
          t ^ n • (c n + t • ∑' m, t ^ m • c (m + (n + 1))) := by
      intro t ht
      have hs : Summable fun m => t ^ m • c m := (summable_pow_smul_of_norm_le hsum ht).of_norm
      rw [← hs.sum_add_tsum_nat_add n, ((summable_nat_add_iff n).2 hs).tsum_eq_zero_add]
      congr 1
      rw [smul_add, zero_add, ← tsum_const_smul'' t, ← tsum_const_smul'' (t ^ n)]
      congr 1
      refine tsum_congr fun m => ?_
      rw [smul_smul, smul_smul, ← pow_succ, ← pow_add]
      congr 2 <;> omega
    -- membership of `cₙ + t T(t)` for `0 < ‖t‖ < r`
    have hmem : ∀ t : 𝕂, 0 < ‖t‖ → ‖t‖ < r →
        c n + t • ∑' m, t ^ m • c (m + (n + 1)) ∈ 𝔤 := by
      intro t ht0 htr
      have ht : t ≠ 0 := norm_pos_iff.mp ht0
      have h1 := hf t ht0 htr
      rw [hsplit t htr.le] at h1
      have h2 : t ^ n • (c n + t • ∑' m, t ^ m • c (m + (n + 1))) ∈ 𝔤 := by
        have h2' : (∑ i ∈ Finset.range n, t ^ i • c i) ∈ 𝔤 :=
          𝔤.sum_mem fun i hi => 𝔤.smul_mem (t ^ i) (ih i (Finset.mem_range.mp hi))
        have := 𝔤.sub_mem h1 h2'
        rwa [add_sub_cancel_left] at this
      have h3 := 𝔤.smul_mem ((t ^ n)⁻¹) h2
      rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero n ht), one_smul] at h3
    -- limit as `t → 0`
    have htend : Tendsto (fun t : 𝕂 => c n + t • ∑' m, t ^ m • c (m + (n + 1)))
        (𝓝[≠] (0 : 𝕂)) (𝓝 (c n)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hlim : Tendsto (fun t : 𝕂 => C * ‖t‖) (𝓝[≠] (0 : 𝕂)) (𝓝 0) := by
        have : Tendsto (fun t : 𝕂 => C * ‖t‖) (𝓝 (0 : 𝕂)) (𝓝 (C * ‖(0 : 𝕂)‖)) :=
          (continuous_const.mul continuous_norm).tendsto 0
        rw [norm_zero, mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
      have hball : Metric.ball (0 : 𝕂) r ∈ 𝓝[≠] (0 : 𝕂) :=
        nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hr)
      filter_upwards [hball] with t ht
      rw [Metric.mem_ball, dist_zero_right] at ht
      rw [add_sub_cancel_left, norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hTbound t ht.le) (norm_nonneg _)
    refine hclosed.mem_of_tendsto htend ?_
    have hball : Metric.ball (0 : 𝕂) r ∈ 𝓝[≠] (0 : 𝕂) :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hr)
    filter_upwards [hball, self_mem_nhdsWithin] with t ht ht0
    rw [Metric.mem_ball, dist_zero_right] at ht
    exact hmem t (norm_pos_iff.mpr ht0) ht

end Coefficients

section Main

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- **Every homogeneous BCH component is a Lie element** (analytic form, Proposition 8.1 (ii)):
for a closed Lie subalgebra `𝔤` and `X, Y ∈ 𝔤`, `Zₙ(X, Y) ∈ 𝔤` for every `n`. -/
theorem bchHom_mem {𝔤 : Submodule 𝕂 𝔸} (h𝔤 : IsClosedLieSubalgebra 𝔤) {X Y : 𝔸}
    (hX : X ∈ 𝔤) (hY : Y ∈ 𝔤) (n : ℕ) : bchHom 𝕂 X Y n ∈ 𝔤 := by
  obtain ⟨δ, hδ, hδmem⟩ := exists_delta_mlog_mem (𝕂 := 𝕂) (𝔸 := 𝔸)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set s : ℝ := ‖X‖ + ‖Y‖ with hs
  have hs0 : 0 ≤ s := add_nonneg (norm_nonneg _) (norm_nonneg _)
  set r : ℝ := min δ (Real.log 2) / (2 * (s + 1)) with hr
  have hmin : 0 < min δ (Real.log 2) := lt_min hδ hlog2
  have hr0 : 0 < r := by positivity
  have hrs : r * s < min δ (Real.log 2) := by
    rw [hr, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hrδ : r * s < δ := hrs.trans_le (min_le_left _ _)
  have hrlog : r * s < Real.log 2 := hrs.trans_le (min_le_right _ _)
  -- the scaled elements
  have hscale : ∀ t : 𝕂, ‖t‖ ≤ r → ‖t • X‖ + ‖t • Y‖ = ‖t‖ * s := fun t _ => by
    rw [norm_smul, norm_smul, hs]; ring
  -- absolute convergence with the weight `rⁿ`
  have hsum : Summable fun m => r ^ m * ‖bchHom 𝕂 X Y m‖ := by
    have h := summable_norm_bchHom (𝕂 := 𝕂) (X := (r : 𝕂) • X) (Y := (r : 𝕂) • Y)
      (by rw [hscale (r : 𝕂) (by rw [RCLike.norm_ofReal, abs_of_pos hr0]),
        RCLike.norm_ofReal, abs_of_pos hr0]; exact hrlog)
    refine h.congr fun m => ?_
    rw [bchHom_smul, norm_smul, norm_pow, RCLike.norm_ofReal, abs_of_pos hr0]
  refine mem_of_tsum_smul_mem h𝔤.isClosed hr0 hsum (fun t ht0 htr => ?_) n
  have hts : ‖t • X‖ + ‖t • Y‖ < min δ (Real.log 2) := by
    rw [hscale t htr.le]
    calc ‖t‖ * s ≤ r * s := mul_le_mul_of_nonneg_right htr.le hs0
      _ < _ := hrs
  have h1 : (∑' m, t ^ m • bchHom 𝕂 X Y m) = mlog 𝕂 (exp (t • X) * exp (t • Y) - 1) := by
    rw [← tsum_bchHom_eq_mlog (hts.trans_le (min_le_right _ _))]
    exact tsum_congr fun m => (bchHom_smul t X Y m).symm
  rw [h1]
  exact hδmem 𝔤 h𝔤 _ _ (𝔤.smul_mem t hX) (𝔤.smul_mem t hY) (hts.trans_le (min_le_left _ _))

end Main

end BCH
