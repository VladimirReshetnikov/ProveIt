/-
# The logarithmic differential equation (Theorem 6.1)

This file formalizes the analytic statement of Theorem 6.1 of the accompanying
article (`docs/combined`): for `X, Y` in a sufficiently small neighborhood of
`(0, 0)` in a real or complex unital Banach algebra, the curve
`Z(t) = log(e^X e^{tY})` (the Mercator logarithm, equal to the BCH series
`∑ₙ Zₙ(X, tY)`) satisfies

  `Z'(t) = β(ad_{Z(t)}) Y`,  `Z(0) = X`,

where `β(ad_Z) = ∑ₙ b⁺ₙ ad_Zⁿ` is the operator of `BCH.Bernoulli`
(`exists_delta_bch_ode`).

## Method

By the inverse function theorem, `exp` has a local inverse `g` near `0`
(`exp` is strictly differentiable at `0` with derivative the identity,
`hasStrictFDerivAt_exp_zero`). For small `X, Y` the curve `y(t) = e^X e^{tY}`
stays in the domain of `g`, and `g(y(t))` is a logarithm of `e^X e^{tY}` of
norm `< log 2`, hence equals `Z(t)` by the uniqueness of the small logarithm
(Proposition 7.4, `BCH.Unique`). At every point `A' = g(y(t))`, `exp` is
strictly differentiable (it is analytic) with the invertible differential
`(dexp)_{A'} = e^{A'} ∘ φ(ad_{A'})` of Theorem 5.2, whose inverse is
`β(ad_{A'}) ∘ e^{-A'}`; the inverse function theorem then gives
`g'(y(t)) = β(ad_{A'}) e^{-A'}`, and the chain rule with `y'(t) = e^X e^{tY} Y
= e^{Z(t)} Y` yields `Z'(t) = β(ad_{Z(t)}) Y`.
-/
import BCH.Bernoulli
import BCH.Unique
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

open NormedSpace Filter Topology

namespace BCH

section IFT

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- `exp` is strictly differentiable at every point, with differential `dexp 𝕂 A`. -/
theorem hasStrictFDerivAt_exp (A : 𝔸) : HasStrictFDerivAt exp (dexp 𝕂 A) A := by
  have h := (exp_analytic (𝕂 := 𝕂) A).hasStrictFDerivAt
  rwa [(hasFDerivAt_exp (𝕂 := 𝕂) A).fderiv] at h

/-- For `‖A‖ < 1/2` the differential `(dexp)_A` is invertible, with inverse
`β(ad_A) ∘ e^{-A}`. -/
noncomputable def dexpEquiv (A : 𝔸) (hA : ‖A‖ < 1 / 2) : 𝔸 ≃L[𝕂] 𝔸 :=
  ContinuousLinearEquiv.equivOfInverse (dexp 𝕂 A)
    ((betaAd 𝕂 A).comp (ContinuousLinearMap.mul 𝕂 𝔸 (exp (-A))))
    (fun x => by
      let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', dexp_apply]
      rw [← mul_assoc, exp_neg_mul_exp, one_mul, betaAd_phiAd_apply hA])
    (fun x => by
      let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', dexp_apply]
      rw [phiAd_betaAd_apply hA, ← mul_assoc, exp_mul_exp_neg, one_mul])

lemma dexpEquiv_coe (A : 𝔸) (hA : ‖A‖ < 1 / 2) :
    ((dexpEquiv A hA : 𝔸 ≃L[𝕂] 𝔸) : 𝔸 →L[𝕂] 𝔸) = dexp 𝕂 A := rfl

lemma dexpEquiv_symm_apply (A : 𝔸) (hA : ‖A‖ < 1 / 2) (y : 𝔸) :
    (dexpEquiv A hA : 𝔸 ≃L[𝕂] 𝔸).symm y = betaAd 𝕂 A (exp (-A) * y) := rfl

end IFT

section ODE

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

lemma half_lt_log_two : (1 : ℝ) / 2 < Real.log 2 := by
  rw [Real.lt_log_iff_exp_lt two_pos]
  have h := Real.add_one_lt_exp (by norm_num : (-(1 / 2 : ℝ)) ≠ 0)
  have hpos : 0 < Real.exp (-(1 / 2 : ℝ)) := Real.exp_pos _
  have hinv : Real.exp (1 / 2) = (Real.exp (-(1 / 2 : ℝ)))⁻¹ := by
    rw [Real.exp_neg, inv_inv]
  rw [hinv, inv_lt_comm₀ hpos two_pos]
  linarith

/-- **Theorem 6.1 (logarithmic differential equation)**: there is `δ > 0` such that for
`‖X‖ + ‖Y‖ < δ` the curve `Z(t) = log(e^X e^{tY})` satisfies `Z(0) = X` and
`Z'(t) = β(ad_{Z(t)}) Y` for `‖t‖ ≤ 1` (and, as recorded for later use, `‖Z(t)‖ < 1/8`). -/
theorem exists_delta_bch_ode :
    ∃ δ : ℝ, 0 < δ ∧ ∀ X Y : 𝔸, ‖X‖ + ‖Y‖ < δ →
      mlog 𝕂 (exp X * exp ((0 : 𝕂) • Y) - 1) = X ∧
      (∀ t : 𝕂, ‖t‖ ≤ 1 → ‖mlog 𝕂 (exp X * exp (t • Y) - 1)‖ < 1 / 8) ∧
      ∀ t : 𝕂, ‖t‖ ≤ 1 →
        HasDerivAt (fun t : 𝕂 => mlog 𝕂 (exp X * exp (t • Y) - 1))
          (betaAd 𝕂 (mlog 𝕂 (exp X * exp (t • Y) - 1)) Y) t := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  -- the local inverse of `exp` at `0`
  have hf0 : HasStrictFDerivAt exp
      ((ContinuousLinearEquiv.refl 𝕂 𝔸 : 𝔸 ≃L[𝕂] 𝔸) : 𝔸 →L[𝕂] 𝔸) (0 : 𝔸) := by
    have h := hasStrictFDerivAt_exp_zero (𝕂 := 𝕂) (𝔸 := 𝔸)
    rw [ContinuousLinearMap.one_def] at h
    exact h
  set e := hf0.toOpenPartialHomeomorph exp with he
  have hecoe : ∀ x, e x = exp x := fun x => by
    rw [he, hf0.toOpenPartialHomeomorph_coe]
  have h0src : (0 : 𝔸) ∈ e.source := hf0.mem_toOpenPartialHomeomorph_source
  have h1tgt : (1 : 𝔸) ∈ e.target := by
    have := hf0.image_mem_toOpenPartialHomeomorph_target
    rwa [exp_zero] at this
  have hsymm1 : e.symm 1 = 0 := by
    have := e.left_inv h0src
    rwa [hecoe, exp_zero] at this
  -- a ball around `1` inside the target on which `‖e.symm y‖ < 1/2`
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, ∀ y : 𝔸, dist y 1 < ε →
      y ∈ e.target ∧ ‖e.symm y‖ < 1 / 8 := by
    have h1 : e.target ∈ 𝓝 (1 : 𝔸) := e.open_target.mem_nhds h1tgt
    have h2 : {y : 𝔸 | ‖e.symm y‖ < 1 / 8} ∈ 𝓝 (1 : 𝔸) := by
      have hcont : ContinuousAt e.symm 1 := e.continuousAt_symm h1tgt
      have hb : Metric.ball (0 : 𝔸) (1 / 8) ∈ 𝓝 (e.symm 1) := by
        rw [hsymm1]; exact Metric.ball_mem_nhds _ (by norm_num)
      have := hcont.preimage_mem_nhds hb
      simpa only [Set.preimage, Metric.mem_ball, dist_zero_right] using this
    obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem h1 h2)
    exact ⟨ε, hε, fun y hy => h (Metric.mem_ball.mpr hy)⟩
  -- the smallness parameter
  have hlogε : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set δ : ℝ := min (Real.log (1 + ε) / 2) (Real.log 2 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ, hδ0, fun X Y hXY => ?_⟩
  have hsmall : ∀ t : 𝕂, ‖t‖ < 2 →
      ‖X‖ + ‖t • Y‖ < Real.log 2 ∧ dist (exp X * exp (t • Y)) 1 < ε := by
    intro t ht
    have hnorm : ‖X‖ + ‖t • Y‖ < 2 * δ := by
      rw [norm_smul]
      have := norm_nonneg X; have := norm_nonneg Y
      nlinarith [norm_nonneg t]
    have hmin1 := min_le_left (Real.log (1 + ε) / 2) (Real.log 2 / 2)
    have hmin2 := min_le_right (Real.log (1 + ε) / 2) (Real.log 2 / 2)
    rw [← hδ] at hmin1 hmin2
    constructor
    · linarith
    · rw [dist_eq_norm]
      have h := norm_exp_mul_exp_sub_one_le 𝕂 X (t • Y)
      have h2 : Real.exp (‖X‖ + ‖t • Y‖) < 1 + ε := by
        calc Real.exp (‖X‖ + ‖t • Y‖) < Real.exp (Real.log (1 + ε)) :=
              Real.exp_lt_exp.mpr (by linarith)
          _ = 1 + ε := Real.exp_log (by linarith)
      linarith
  have hhalf : (1 : ℝ) / 2 < Real.log 2 := half_lt_log_two
  -- identification of `Z(t)` with the local inverse
  have hZ : ∀ t : 𝕂, ‖t‖ < 2 →
      mlog 𝕂 (exp X * exp (t • Y) - 1) = e.symm (exp X * exp (t • Y)) := by
    intro t ht
    obtain ⟨hn, hd⟩ := hsmall t ht
    obtain ⟨htgt, hlt⟩ := hball _ hd
    have hexp : exp (e.symm (exp X * exp (t • Y))) = exp X * exp (t • Y) := by
      have := e.right_inv htgt
      rwa [hecoe] at this
    rw [← tsum_bchHom_eq_mlog hn]
    exact (eq_tsum_bchHom_of_exp_eq hn (hlt.trans (by linarith)) hexp).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [zero_smul, exp_zero, mul_one]
    have h := (hsmall 0 (by simp)).1
    rw [zero_smul, norm_zero, add_zero] at h
    exact mlog_exp_sub_one h
  · intro t ht
    have ht2 : ‖t‖ < 2 := by linarith
    obtain ⟨hn, hd⟩ := hsmall t ht2
    obtain ⟨htgt, hlt⟩ := hball _ hd
    rw [hZ t ht2]
    exact hlt
  · intro t ht
    have ht2 : ‖t‖ < 2 := by linarith
    have hcurve : HasDerivAt (fun t : 𝕂 => exp X * exp (t • Y))
        (exp X * (exp (t • Y) * Y)) t :=
      (hasDerivAt_exp_smul_const Y t).const_mul (exp X)
    obtain ⟨hn, hd⟩ := hsmall t ht2
    obtain ⟨htgt, hlt⟩ := hball _ hd
    set A' := e.symm (exp X * exp (t • Y)) with hA'
    have hA'src : A' ∈ e.source := e.map_target htgt
    have hexpA' : exp A' = exp X * exp (t • Y) := by
      have := e.right_inv htgt
      rwa [hecoe] at this
    have hlt2 : ‖A'‖ < 1 / 2 := by rw [hA']; linarith
    have hstrict : HasStrictFDerivAt exp
        ((dexpEquiv A' hlt2 : 𝔸 ≃L[𝕂] 𝔸) : 𝔸 →L[𝕂] 𝔸) A' :=
      hasStrictFDerivAt_exp A'
    have hleft : ∀ᶠ x in 𝓝 A', e.symm (exp x) = x := by
      filter_upwards [e.open_source.mem_nhds hA'src] with x hx
      rw [← hecoe]
      exact e.left_inv hx
    have hg := hstrict.to_local_left_inverse hleft
    rw [hexpA'] at hg
    have hcomp := hg.hasFDerivAt.comp_hasDerivAt t hcurve
    have heq : (fun s : 𝕂 => mlog 𝕂 (exp X * exp (s • Y) - 1)) =ᶠ[𝓝 t]
        (e.symm ∘ fun s : 𝕂 => exp X * exp (s • Y)) := by
      filter_upwards [Metric.ball_mem_nhds t (by linarith : (0 : ℝ) < 2 - ‖t‖)] with s hs
      rw [Metric.mem_ball, dist_eq_norm] at hs
      have hs2 : ‖s‖ < 2 := by
        calc ‖s‖ = ‖(s - t) + t‖ := by rw [sub_add_cancel]
          _ ≤ ‖s - t‖ + ‖t‖ := norm_add_le _ _
          _ < 2 := by linarith
      exact hZ s hs2
    refine (hcomp.congr_of_eventuallyEq heq).congr_deriv ?_
    rw [hZ t ht2, ← hA']
    show (dexpEquiv A' hlt2 : 𝔸 ≃L[𝕂] 𝔸).symm (exp X * (exp (t • Y) * Y)) = betaAd 𝕂 A' Y
    rw [dexpEquiv_symm_apply, ← mul_assoc (exp X), ← hexpA', ← mul_assoc, exp_neg_mul_exp,
      one_mul]

/-- **Theorem 6.1, converse (uniqueness)**: if `Z` solves `Z'(t) = β(ad_{Z(t)}) Y` with
`Z(0) = X` on a disc `‖t‖ < r`, `r > 1`, with `‖Z(t)‖ < 1/2` there, and `‖X‖ + ‖Y‖ < log 2`,
then `Z(t) = log(e^X e^{tY})` for `‖t‖ ≤ 1`. -/
theorem bch_ode_unique {X Y : 𝔸} {Z : 𝕂 → 𝔸} {r : ℝ} (hr : 1 < r)
    (hZ : ∀ t : 𝕂, ‖t‖ < r → HasDerivAt Z (betaAd 𝕂 (Z t) Y) t)
    (hZ0 : Z 0 = X) (hsmall : ∀ t : 𝕂, ‖t‖ < r → ‖Z t‖ < 1 / 2)
    (hXY : ‖X‖ + ‖Y‖ < Real.log 2) :
    ∀ t : 𝕂, ‖t‖ ≤ 1 → Z t = mlog 𝕂 (exp X * exp (t • Y) - 1) := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  set B : Set 𝕂 := Metric.ball (0 : 𝕂) r with hB
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hBconn : IsPreconnected B := (convex_ball (0 : 𝕂) r).isPreconnected
  have hmem : ∀ t : 𝕂, t ∈ B ↔ ‖t‖ < r := fun t => by
    rw [hB, Metric.mem_ball, dist_zero_right]
  -- `H(t) = e^{Z(t)} e^{-tY}` has zero derivative
  let H : 𝕂 → 𝔸 := fun t => exp (Z t) * exp (t • (-Y))
  have hH : ∀ t ∈ B, HasDerivAt H 0 t := by
    intro t ht
    rw [hmem] at ht
    have h1 : HasDerivAt (fun s => exp (Z s)) (exp (Z t) * Y) t := by
      have := hasDerivAt_exp_comp (𝕂 := 𝕂) (hZ t ht)
      rwa [dexp_apply, phiAd_betaAd_apply (hsmall t ht)] at this
    have h2 : HasDerivAt (fun s : 𝕂 => exp (s • (-Y))) (exp (t • (-Y)) * -Y) t :=
      hasDerivAt_exp_smul_const (-Y) t
    refine (h1.mul h2).congr_deriv ?_
    have hc : exp (t • (-Y)) * Y = Y * exp (t • (-Y)) :=
      ((((Commute.refl Y).neg_right).smul_right t).exp_right).eq.symm
    calc exp (Z t) * Y * exp (t • (-Y)) + exp (Z t) * (exp (t • (-Y)) * -Y)
        = exp (Z t) * (Y * exp (t • (-Y))) - exp (Z t) * (exp (t • (-Y)) * Y) := by
          noncomm_ring
      _ = 0 := by rw [hc, sub_self]
  have hdiff : DifferentiableOn 𝕂 H B :=
    fun t ht => (hH t ht).differentiableAt.differentiableWithinAt
  have hd0 : B.EqOn (deriv H) 0 := fun t ht => (hH t ht).deriv
  have h0B : (0 : 𝕂) ∈ B := by rw [hmem, norm_zero]; linarith
  have hH0 : H 0 = exp X := by
    simp only [H, hZ0, zero_smul, exp_zero, mul_one]
  intro t ht
  have htB : t ∈ B := by rw [hmem]; linarith
  have hconst : H t = H 0 := hBopen.is_const_of_deriv_eq_zero hBconn hdiff hd0 htB h0B
  rw [hH0] at hconst
  have hconst' : exp (Z t) * exp (t • (-Y)) = exp X := hconst
  have hexp : exp (Z t) = exp X * exp (t • Y) := by
    calc exp (Z t) = exp (Z t) * exp (t • (-Y)) * exp (t • Y) := by
          rw [mul_assoc, smul_neg, exp_neg_mul_exp, mul_one]
      _ = exp X * exp (t • Y) := by rw [hconst']
  have hn : ‖X‖ + ‖t • Y‖ < Real.log 2 := by
    rw [norm_smul]
    have : ‖t‖ * ‖Y‖ ≤ ‖Y‖ := mul_le_of_le_one_left (norm_nonneg _) ht
    linarith
  have hZt : ‖Z t‖ < Real.log 2 := (hsmall t ((hmem t).mp htB)).trans half_lt_log_two
  rw [← tsum_bchHom_eq_mlog hn]
  exact eq_tsum_bchHom_of_exp_eq hn hZt hexp

end ODE

end BCH
