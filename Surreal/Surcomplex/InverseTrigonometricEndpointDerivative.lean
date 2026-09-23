import Surreal.Surcomplex.AcosEndpointSeries

/-!
# No surreal derivative at the inverse-sine endpoints

The square-root endpoint expansion implies that inward difference quotients
exceed every fixed surreal bound, including infinite bounds. This establishes
`trigonometry:rem:noendpointderivative` using the full native tolerance class.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

@[simp] theorem arccosFunction_one : arccosFunction (1 : SignSequence.{u}) = 0 := by
  have hpi : (0 : SignSequence.{u}) ≤ SignSequence.ofReal Real.pi := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono.monotone Real.pi_pos.le
  have he := arccos_finiteCos (0 : SignSequence.FiniteElement.{u}) ⟨le_rfl, hpi⟩
  have he' : arccos ⟨(1 : SignSequence.{u}), by norm_num⟩ = 0 := by simpa using he
  rw [arccosFunction_eq ⟨1, by norm_num⟩, he']
  rfl

@[simp] theorem arcsinFunction_one :
    arcsinFunction (1 : SignSequence.{u}) = SignSequence.ofReal (Real.pi / 2) := by
  have h := arccosFunction_one.{u}
  change SignSequence.ofReal (Real.pi / 2) - arcsinFunction 1 = 0 at h
  exact (sub_eq_zero.mp h).symm

private theorem half_lt_endpoint_factor {R : SignSequence.{u}}
    (hR : SignSequence.IsFinite R) (hr : SignSequence.standardPart R = 1) : 1 / 2 < R := by
  have hi := SignSequence.infinitesimal_sub_standardPart hR
  rw [hr, map_one] at hi
  have hb := (SignSequence.isInfinitesimal_iff_forall_real_abs_lt _).mp hi (1 / 2) (by norm_num)
  norm_num only [map_div₀, map_one, map_ofNat] at hb
  have hl := (abs_lt.mp hb).1
  linarith only [hl]

/-- The endpoint angle divided by its defect exceeds every fixed surreal bound locally. -/
theorem arccosFunction_endpoint_quotient_unbounded (M : SignSequence.{u}) :
    ∃ δ : SignSequence.{u}, 0 < δ ∧ ∀ τ : SignSequence.{u}, 0 < τ → τ < δ →
      M < arccosFunction (1 - τ) / τ := by
  let B := |M| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨min (SignSequence.ofOrdinal Ordinal.omega0)⁻¹ (1 / (2 * B ^ 2)),
    lt_min SignSequence.inv_omega0_pos (by positivity), ?_⟩
  intro τ hp ht
  have hi : SignSequence.IsInfinitesimal τ := by
    apply SignSequence.infinitesimal_of_abs_le (y := (SignSequence.ofOrdinal Ordinal.omega0)⁻¹)
      _ SignSequence.infinitesimal_inv_omega0
    rw [abs_of_pos hp, abs_of_pos SignSequence.inv_omega0_pos]
    exact (lt_min_iff.mp ht).1.le
  obtain ⟨R, hR, hr, he⟩ := arccosFunction_endpoint_leading_factor τ hp hi
  have hhalf := half_lt_endpoint_factor hR hr
  have hb := (lt_div_iff₀ (show 0 < 2 * B ^ 2 by positivity)).mp (lt_min_iff.mp ht).2
  have hb' := mul_lt_mul_of_pos_right hb hp
  have hs := SignSequence.sqrt_sq (show 0 ≤ 2 * τ by positivity)
  have hspos := SignSequence.sqrt_pos (show 0 < 2 * τ by positivity)
  have hsmall : B * τ < SignSequence.sqrt (2 * τ) / 2 := by
    nlinarith only [hb', hs, hspos, mul_pos hB hp]
  have hscale := mul_lt_mul_of_pos_left hhalf hspos
  have hbound : B < arccosFunction (1 - τ) / τ := by
    apply (lt_div_iff₀ hp).mpr
    rw [he]
    linarith only [hsmall, hscale]
  exact (show M < B by dsimp [B]; linarith only [le_abs_self M]).trans hbound

/-- Inward difference quotients at one exceed every fixed surreal bound. -/
theorem arcsinFunction_endpoint_quotient_unbounded (M : SignSequence.{u}) :
    ∃ δ : SignSequence.{u}, 0 < δ ∧ ∀ τ : SignSequence.{u}, 0 < τ → τ < δ →
      M < (arcsinFunction (1 - τ) - arcsinFunction 1) / (-τ) := by
  obtain ⟨δ, hδ, h⟩ := arccosFunction_endpoint_quotient_unbounded M
  refine ⟨δ, hδ, fun τ hp ht => ?_⟩
  convert h τ hp ht using 1
  rw [arcsinFunction_one, arccosFunction]
  ring

/-- Even the inward, domain-restricted derivative at one has no surreal value. -/
theorem not_arcsinFunction_left_derivative_one (d : SignSequence.{u}) :
    ¬ (∀ ε : SignSequence.{u}, 0 < ε → ∃ r : SignSequence.{u}, 0 < r ∧
      ∀ τ : SignSequence.{u}, 0 < τ → τ < r → τ < 1 →
        |(arcsinFunction (1 - τ) - arcsinFunction 1) / (-τ) - d| < ε) := by
  intro hd
  obtain ⟨r, hr, hd⟩ := hd 1 (by norm_num)
  obtain ⟨δ, hδ, hq⟩ := arcsinFunction_endpoint_quotient_unbounded (d + 1)
  let τ := min r (min δ 1) / 2
  have hmin : (0 : SignSequence.{u}) < min r (min δ 1) := lt_min hr (lt_min hδ zero_lt_one)
  have hp : 0 < τ := half_pos hmin
  have hsmall : τ < min r (min δ 1) := half_lt_self hmin
  have htr : τ < r := hsmall.trans_le (min_le_left _ _)
  have htδ : τ < δ := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htone : τ < 1 := hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hbound := (abs_lt.mp (hd τ hp htr htone)).2
  have hlarge := hq τ hp htδ
  linarith only [hbound, hlarge]

/-- No actual surreal value, finite or infinite, is a fine derivative at one. -/
theorem not_fineHasDerivAt_arcsinFunction_one (d : SignSequence.{u}) :
    ¬ FineHasDerivAt arcsinFunction d 1 := by
  intro hd
  apply not_arcsinFunction_left_derivative_one d
  intro ε hε
  obtain ⟨r, hr, h⟩ := (SignSequence.fineHasDerivAt_iff _ _ _).mp hd ε hε
  refine ⟨r, hr, fun τ hp ht _ => ?_⟩
  have he := h (-τ) (neg_ne_zero.mpr hp.ne') (by rwa [abs_neg, abs_of_pos hp])
  simpa only [sub_eq_add_neg] using he

/-- Geometric inverse sine is odd on its whole actual closed domain. -/
theorem arcsinFunction_neg_of_mem {x : SignSequence.{u}} (hx : x ∈ Set.Icc (-1) 1) :
    arcsinFunction (-x) = -arcsinFunction x := by
  have hn : -x ∈ Set.Icc (-1) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hθ := arcsin_mem ⟨x, hx⟩
  have hneg : (-arcsin ⟨x, hx⟩).val ∈ Set.Icc
      (SignSequence.ofReal (-(Real.pi / 2))) (SignSequence.ofReal (Real.pi / 2)) := by
    change SignSequence.ofReal (-(Real.pi / 2)) ≤ -(arcsin ⟨x, hx⟩).val ∧
      -(arcsin ⟨x, hx⟩).val ≤ SignSequence.ofReal (Real.pi / 2)
    simp only [Set.mem_Icc, map_neg] at hθ ⊢
    constructor <;> linarith only [hθ.1, hθ.2]
  have he := arcsin_finiteSin (-arcsin ⟨x, hx⟩) hneg
  have he' : arcsin ⟨-x, hn⟩ = -arcsin ⟨x, hx⟩ := by
    simpa only [finiteSin_neg, finiteSin_arcsin] using he
  rw [arcsinFunction_eq ⟨-x, hn⟩, arcsinFunction_eq ⟨x, hx⟩, he']
  rfl

private theorem arcsin_endpoint_slopes_eq (τ : SignSequence.{u}) (hp : 0 < τ) (ht : τ < 1) :
    (arcsinFunction (-1 + τ) - arcsinFunction (-1)) / τ =
      (arcsinFunction (1 - τ) - arcsinFunction 1) / (-τ) := by
  have hx : 1 - τ ∈ Set.Icc (-1) 1 := by constructor <;> linarith only [hp, ht]
  rw [show -1 + τ = -(1 - τ) by ring, arcsinFunction_neg_of_mem hx,
    arcsinFunction_neg_of_mem (show (1 : SignSequence.{u}) ∈ Set.Icc (-1) 1 by norm_num)]
  ring

/-- The inward quotients at minus one also exceed every fixed surreal bound. -/
theorem arcsinFunction_neg_endpoint_quotient_unbounded (M : SignSequence.{u}) :
    ∃ δ : SignSequence.{u}, 0 < δ ∧ ∀ τ : SignSequence.{u}, 0 < τ → τ < δ →
      M < (arcsinFunction (-1 + τ) - arcsinFunction (-1)) / τ := by
  obtain ⟨δ, hδ, h⟩ := arcsinFunction_endpoint_quotient_unbounded M
  refine ⟨min δ 1, lt_min hδ zero_lt_one, fun τ hp ht => ?_⟩
  rw [arcsin_endpoint_slopes_eq τ hp (lt_min_iff.mp ht).2]
  exact h τ hp (lt_min_iff.mp ht).1

/-- The inward, domain-restricted derivative at minus one has no surreal value. -/
theorem not_arcsinFunction_right_derivative_neg_one (d : SignSequence.{u}) :
    ¬ (∀ ε : SignSequence.{u}, 0 < ε → ∃ r : SignSequence.{u}, 0 < r ∧
      ∀ τ : SignSequence.{u}, 0 < τ → τ < r → τ < 1 →
        |(arcsinFunction (-1 + τ) - arcsinFunction (-1)) / τ - d| < ε) := by
  intro hd
  apply not_arcsinFunction_left_derivative_one d
  intro ε hε
  obtain ⟨r, hr, h⟩ := hd ε hε
  refine ⟨r, hr, fun τ hp ht hone => ?_⟩
  rw [← arcsin_endpoint_slopes_eq τ hp hone]
  exact h τ hp ht hone

/-- No finite or infinite actual surreal is a fine derivative at minus one. -/
theorem not_fineHasDerivAt_arcsinFunction_neg_one (d : SignSequence.{u}) :
    ¬ FineHasDerivAt arcsinFunction d (-1) := by
  intro hd
  apply not_arcsinFunction_right_derivative_neg_one d
  intro ε hε
  obtain ⟨r, hr, h⟩ := (SignSequence.fineHasDerivAt_iff _ _ _).mp hd ε hε
  refine ⟨r, hr, fun τ hp ht _ => ?_⟩
  exact h τ hp.ne' (by rwa [abs_of_pos hp])

end
end Surreal.Surcomplex
