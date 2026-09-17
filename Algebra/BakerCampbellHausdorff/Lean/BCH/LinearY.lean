/-
# The terms of the BCH series linear in `Y` (Corollary 6.4)

Corollary 6.4 of the accompanying article (`docs/combined`) states that the
part of `Z(X, Y)` linear in `Y` is `β(ad_X) Y = ∑ₙ (Bₙ⁺/n!) ad_Xⁿ Y`, i.e.
`Z(X, εY) = X + ε β(ad_X) Y + O(ε²)`. Analytically this is the statement that
`t ↦ Z(X, tY)` is differentiable at `t = 0` with derivative `β(ad_X) Y`, which
is the logarithmic differential equation of `BCH.ODE` at `t = 0` together with
the identification `Z(X, 0) = X` and the Bernoulli identification of
`BCH.BernoulliNumbers`.

* `exists_delta_hasDerivAt_bch_linearY`: for `‖X‖ + ‖Y‖` small,
  `HasDerivAt (fun t => ∑ₙ Zₙ(X, tY)) (∑ₙ (Bₙ⁺/n!) • ad_Xⁿ Y) 0`.
-/
import BCH.ODE
import BCH.BernoulliNumbers

open NormedSpace Finset Filter Topology

namespace BCH

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- **Corollary 6.4 (all single-`Y` terms)**: for `‖X‖ + ‖Y‖` small, the function
`t ↦ Z(X, tY) = ∑ₙ Zₙ(X, tY)` has derivative `β(ad_X) Y = ∑ₙ (Bₙ⁺/n!) ad_Xⁿ Y` at `t = 0`;
the coefficient of `ad_Xⁿ Y` in the part of `Z(X, Y)` linear in `Y` is `Bₙ⁺/n!`. -/
theorem exists_delta_hasDerivAt_bch_linearY :
    ∃ δ : ℝ, 0 < δ ∧ ∀ X Y : 𝔸, ‖X‖ + ‖Y‖ < δ →
      HasDerivAt (fun t : 𝕂 => ∑' n, bchHom 𝕂 X (t • Y) n)
        (∑' n : ℕ, ((bernoulli' n / n.factorial : ℚ) : 𝕂) • (ad 𝕂 X ^ n) Y) 0 := by
  obtain ⟨δ, hδ, h⟩ := exists_delta_bch_ode (𝕂 := 𝕂) (𝔸 := 𝔸)
  refine ⟨min δ (Real.log 2), lt_min hδ (Real.log_pos one_lt_two), fun X Y hXY => ?_⟩
  have hXYδ : ‖X‖ + ‖Y‖ < δ := hXY.trans_le (min_le_left _ _)
  have hXYlog : ‖X‖ + ‖Y‖ < Real.log 2 := hXY.trans_le (min_le_right _ _)
  obtain ⟨h0, hsmall, hderiv⟩ := h X Y hXYδ
  have hd := hderiv 0 (by simp)
  have hX8 : ‖X‖ < 1 / 8 := by
    have := hsmall 0 (by simp)
    rwa [h0] at this
  rw [h0] at hd
  -- near `t = 0` the Mercator logarithm is the BCH series
  have hfun : (fun t : 𝕂 => ∑' n, bchHom 𝕂 X (t • Y) n) =ᶠ[𝓝 0]
      fun t => mlog 𝕂 (exp X * exp (t • Y) - 1) := by
    filter_upwards [Metric.ball_mem_nhds (0 : 𝕂) one_pos] with t ht
    rw [Metric.mem_ball, dist_zero_right] at ht
    apply tsum_bchHom_eq_mlog
    rw [norm_smul]
    have : ‖t‖ * ‖Y‖ ≤ ‖Y‖ := mul_le_of_le_one_left (norm_nonneg _) ht.le
    linarith
  refine (hd.congr_of_eventuallyEq hfun).congr_deriv ?_
  rw [betaAd_apply (by linarith)]
  refine tsum_congr fun n => ?_
  rw [bplus_eq_bernoulli']

end BCH
