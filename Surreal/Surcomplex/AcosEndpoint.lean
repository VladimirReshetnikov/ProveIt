import Surreal.Surcomplex.ArcsinSeries
import Surreal.Foundations.SignSequenceSqrtInfinitesimal

/-!
# Square-root ramification at the inverse-cosine endpoint

The exact half-angle identity and the inverse-sine strong series establish
`trigonometry:prop:acosendpoint`, with the actual square-root scale and a
finite normalized remainder.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

private theorem infinitesimal_half {τ : SignSequence.{u}} (hp : 0 < τ)
    (hi : SignSequence.IsInfinitesimal τ) : SignSequence.IsInfinitesimal (τ / 2) := by
  apply SignSequence.infinitesimal_of_abs_le (y := τ) _ hi
  rw [abs_of_pos hp, abs_of_pos (div_pos hp (by norm_num))]
  linarith

private theorem endpoint_sqrt_mem {τ : SignSequence.{u}} (hp : 0 < τ)
    (hi : SignSequence.IsInfinitesimal τ) :
    SignSequence.sqrt (τ / 2) ∈ Set.Icc (-1) 1 := by
  have hs := SignSequence.infinitesimal_sqrt (by positivity : 0 ≤ τ / 2) (infinitesimal_half hp hi)
  have hb := (SignSequence.isInfinitesimal_iff_forall_real_abs_lt _).mp hs 1 (by norm_num)
  rw [map_one, abs_of_nonneg (SignSequence.sqrt_nonneg _)] at hb
  exact ⟨by linarith [SignSequence.sqrt_nonneg (τ / 2)], hb.le⟩

/-- The two square-root scales in the half-angle identity differ by exactly two. -/
theorem sqrt_two_mul_eq_two_mul_sqrt_half (τ : SignSequence.{u}) (hτ : 0 ≤ τ) :
    SignSequence.sqrt (2 * τ) = 2 * SignSequence.sqrt (τ / 2) := by
  apply SignSequence.sqrt_eq_of_nonneg_sq
    (mul_nonneg (by norm_num) (SignSequence.sqrt_nonneg _))
  have hs := SignSequence.sqrt_sq (show 0 ≤ τ / 2 by positivity)
  nlinarith only [hs]

private theorem two_arcsin_mem (x : Set.Icc (-1 : SignSequence.{u}) 1)
    (hx : 0 < x.val) :
    (2 * arcsin x).val ∈ Set.Icc 0 (SignSequence.ofReal Real.pi) := by
  have hθ := arcsin_mem x
  have hpos : 0 < (arcsin x).val := by
    by_contra h
    have hz : (0 : SignSequence.FiniteElement.{u}).val ∈ Set.Icc
        (SignSequence.ofReal (-(Real.pi / 2))) (SignSequence.ofReal (Real.pi / 2)) := by
      change SignSequence.ofReal (-(Real.pi / 2)) ≤ 0 ∧ 0 ≤ SignSequence.ofReal (Real.pi / 2)
      have hpi : (0 : SignSequence.{u}) < SignSequence.ofReal (Real.pi / 2) := by
        simpa only [map_zero] using SignSequence.ofReal_strictMono (half_pos Real.pi_pos)
      rw [map_neg]
      exact ⟨neg_nonpos.mpr hpi.le, hpi.le⟩
    have he := finiteSin_strictMonoOn.monotoneOn hθ hz (le_of_not_gt h)
    rw [finiteSin_arcsin, finiteSin_zero] at he
    exact hx.not_ge he
  have hhi := hθ.2
  rw [map_div₀, map_ofNat] at hhi
  change 0 ≤ (2 : SignSequence.{u}) * (arcsin x).val ∧
    2 * (arcsin x).val ≤ SignSequence.ofReal Real.pi
  constructor <;> linarith only [hpos, hhi]

private theorem arccosFunction_finiteCos (θ : SignSequence.FiniteElement.{u})
    (hθ : θ.val ∈ Set.Icc 0 (SignSequence.ofReal Real.pi)) :
    arccosFunction (finiteCos θ) = θ.val := by
  rw [arccosFunction_eq ⟨finiteCos θ, finiteCos_mem_Icc θ⟩, arccos_finiteCos θ hθ]

/-- The endpoint angle is exactly twice the inverse sine of the half-defect square root. -/
theorem arccosFunction_one_sub_eq_two_arcsin (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    arccosFunction (1 - τ) = 2 * arcsinFunction (SignSequence.sqrt (τ / 2)) := by
  let x : Set.Icc (-1 : SignSequence.{u}) 1 :=
    ⟨SignSequence.sqrt (τ / 2), endpoint_sqrt_mem hp hi⟩
  have hx : 0 < x.val := SignSequence.sqrt_pos (by positivity)
  have hc : finiteCos (2 * arcsin x) = 1 - τ := by
    rw [finiteCos_two_mul_eq_sin_sq, finiteSin_arcsin]
    change 1 - 2 * SignSequence.sqrt (τ / 2) ^ 2 = 1 - τ
    rw [SignSequence.sqrt_sq (show 0 ≤ τ / 2 by positivity)]
    ring
  calc
    arccosFunction (1 - τ) = arccosFunction (finiteCos (2 * arcsin x)) := congrArg _ hc.symm
    _ = (2 * arcsin x).val := arccosFunction_finiteCos _ (two_arcsin_mem x hx)
    _ = 2 * arcsinFunction x.val := by rw [arcsinFunction_eq]; rfl

end
end Surreal.Surcomplex
