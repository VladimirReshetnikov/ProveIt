import FabiusFunction.PaperStatements
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The original characterization of Rvachev's function

This file formalizes Theorem 1 of Juan Arias de Reyna,
*An infinitely differentiable function with compact support: Definition and
Properties*, arXiv:1702.05442.  Unlike the bounded-CDF characterization in
`IsFabius`, the paper starts with a compactly supported function `φ` and an
initially unspecified positive constant `k`.

Besides packaging the hypotheses, the file derives the elementary consequences
needed by the Fourier uniqueness argument: the exact ordinary support,
nonnegativity, the translate identity on `[0,1]`, normalization on both the
support interval and the whole real line, and the forced value `k = 2`.
It also proves that the Rvachev fold of every bounded `IsFabius` solution
satisfies this original characterization at scale two.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff Interval
open MeasureTheory Set

namespace Fabius

noncomputable section

/-- The four hypotheses in Theorem 1 of arXiv:1702.05442, including the
initially unspecified positive dilation constant. -/
structure IsOriginalFabius (φ : ℝ → ℝ) (k : ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ φ
  tsupport_eq : tsupport φ = Icc (-1 : ℝ) 1
  pos_of_mem : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < φ x
  value_zero : φ 0 = 1
  scale_pos : 0 < k
  hasDerivAt : ∀ x : ℝ,
    HasDerivAt φ (k * (φ (2 * x + 1) - φ (2 * x - 1))) x

namespace IsOriginalFabius

variable {φ : ℝ → ℝ} {k : ℝ} (h : IsOriginalFabius φ k)

include h

/-- An original solution has compact support in Mathlib's sense. -/
theorem hasCompactSupport : HasCompactSupport φ := by
  rw [HasCompactSupport, h.tsupport_eq]
  exact isCompact_Icc

/-- A solution vanishes strictly outside its prescribed support. -/
theorem eq_zero_of_not_mem {x : ℝ} (hx : x ∉ Icc (-1 : ℝ) 1) : φ x = 0 := by
  by_contra hne
  have hsupp : x ∈ Function.support φ := hne
  have htop : x ∈ tsupport φ := subset_tsupport φ hsupp
  rw [h.tsupport_eq] at htop
  exact hx htop

/-- Smoothness forces a compactly supported solution to vanish at `-1`. -/
theorem value_neg_one : φ (-1) = 0 := by
  have hzclosed : IsClosed {x : ℝ | φ x = 0} :=
    isClosed_eq h.contDiff.continuous continuous_const
  have hsub : Iio (-1 : ℝ) ⊆ {x : ℝ | φ x = 0} := by
    intro x hx
    change x < -1 at hx
    exact h.eq_zero_of_not_mem (by
      intro hm
      change -1 ≤ x ∧ x ≤ 1 at hm
      linarith [hm.1])
  have hmem : (-1 : ℝ) ∈ closure (Iio (-1 : ℝ)) := by
    rw [closure_Iio]
    simp
  exact (closure_minimal hsub hzclosed) hmem

/-- Smoothness forces a compactly supported solution to vanish at `1`. -/
theorem value_one : φ 1 = 0 := by
  have hzclosed : IsClosed {x : ℝ | φ x = 0} :=
    isClosed_eq h.contDiff.continuous continuous_const
  have hsub : Ioi (1 : ℝ) ⊆ {x : ℝ | φ x = 0} := by
    intro x hx
    change 1 < x at hx
    exact h.eq_zero_of_not_mem (by
      intro hm
      change -1 ≤ x ∧ x ≤ 1 at hm
      linarith [hm.2])
  have hmem : (1 : ℝ) ∈ closure (Ioi (1 : ℝ)) := by
    rw [closure_Ioi]
    simp
  exact (closure_minimal hsub hzclosed) hmem

/-- A solution vanishes at and to the left of the support interval. -/
theorem eq_zero_of_le_neg_one {x : ℝ} (hx : x ≤ -1) : φ x = 0 := by
  rcases hx.eq_or_lt with rfl | hxlt
  · exact h.value_neg_one
  · exact h.eq_zero_of_not_mem (by
      intro hxmem
      exact (not_lt_of_ge hxmem.1) hxlt)

/-- A solution vanishes at and to the right of the support interval. -/
theorem eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) : φ x = 0 := by
  rcases hx.eq_or_lt with rfl | hxlt
  · exact h.value_one
  · exact h.eq_zero_of_not_mem (by
      intro hxmem
      exact (not_lt_of_ge hxmem.2) hxlt)

/-- The ordinary support of an original solution is the open interval `(-1,1)`. -/
theorem support_eq : Function.support φ = Ioo (-1 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxopen
    apply hx
    simp only [mem_Ioo, not_and_or, not_lt] at hxopen
    rcases hxopen with hxleft | hxright
    · exact h.eq_zero_of_le_neg_one hxleft
    · exact h.eq_zero_of_one_le hxright
  · intro x hx
    exact ne_of_gt (h.pos_of_mem x hx)

/-- A point outside the open support interval is a zero of an original solution. -/
theorem eq_zero_of_not_mem_Ioo {x : ℝ} (hx : x ∉ Ioo (-1 : ℝ) 1) : φ x = 0 := by
  by_contra hne
  apply hx
  rw [← h.support_eq]
  exact hne

/-- An original solution is nonnegative everywhere. -/
theorem nonneg (x : ℝ) : 0 ≤ φ x := by
  by_cases hx : x ∈ Ioo (-1 : ℝ) 1
  · exact (h.pos_of_mem x hx).le
  · rw [h.eq_zero_of_not_mem_Ioo hx]

/-- Positivity characterizes the interior of the prescribed support. -/
theorem pos_iff_mem_Ioo (x : ℝ) : 0 < φ x ↔ x ∈ Ioo (-1 : ℝ) 1 := by
  constructor
  · intro hx
    rw [← h.support_eq]
    exact ne_of_gt hx
  · exact h.pos_of_mem x

/-- The zero set of an original solution is exactly the complement of
`(-1,1)`.  This packages positivity in the interior together with vanishing at
and beyond both endpoints. -/
theorem eq_zero_iff_not_mem_Ioo (x : ℝ) :
    φ x = 0 ↔ x ∉ Ioo (-1 : ℝ) 1 := by
  constructor
  · intro hx hxmem
    exact (ne_of_gt (h.pos_of_mem x hxmem)) hx
  · exact h.eq_zero_of_not_mem_Ioo

/-- The translate identity `φ(t) + φ(t-1) = 1` on `[0,1]` follows directly
from the differential equation and support.  It is equation (28) of the
paper, before Poisson summation is invoked there. -/
theorem add_shift_eq_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    φ t + φ (t - 1) = 1 := by
  let g : ℝ → ℝ := φ + fun x : ℝ => φ (x - 1)
  have hgcont : ContinuousOn g (Icc (0 : ℝ) 1) := by
    change ContinuousOn (φ + fun x : ℝ => φ (x - 1)) (Icc (0 : ℝ) 1)
    exact (h.contDiff.continuous.add
      (h.contDiff.continuous.comp (continuous_id.sub continuous_const))).continuousOn
  have hgderiv : ∀ x ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt g 0 (Ici x) x := by
    intro x hx
    have hfirst := h.hasDerivAt x
    have hsecond := (h.hasDerivAt (x - 1)).comp_sub_const x 1
    have hadd : HasDerivAt g
        (k * (φ (2 * x + 1) - φ (2 * x - 1)) +
          k * (φ (2 * (x - 1) + 1) - φ (2 * (x - 1) - 1))) x := by
      exact hfirst.add hsecond
    have hfarRight : φ (2 * x + 1) = 0 :=
      h.eq_zero_of_one_le (by linarith [hx.1])
    have hfarLeft : φ (2 * x - 3) = 0 :=
      h.eq_zero_of_le_neg_one (by linarith [hx.2])
    have hcoef :
        k * (φ (2 * x + 1) - φ (2 * x - 1)) +
          k * (φ (2 * (x - 1) + 1) - φ (2 * (x - 1) - 1)) = 0 := by
      rw [show 2 * (x - 1) + 1 = 2 * x - 1 by ring,
        show 2 * (x - 1) - 1 = 2 * x - 3 by ring,
        hfarRight, hfarLeft]
      ring
    have hderiv : HasDerivAt g 0 x := hadd.congr_deriv hcoef
    exact hderiv.hasDerivWithinAt
  have hconst := constant_of_has_deriv_right_zero hgcont hgderiv t ht
  dsimp only [g, Pi.add_apply] at hconst
  change φ t + φ (t - 1) = φ 0 + φ (0 - 1) at hconst
  simpa [h.value_zero, h.value_neg_one] using hconst

/-- The integral of every original solution over its support is one. -/
theorem intervalIntegral_eq_one :
    (∫ x in (-1 : ℝ)..1, φ x) = 1 := by
  have hadd : (∫ x in (0 : ℝ)..1, (φ x + φ (x - 1))) =
      (∫ _x in (0 : ℝ)..1, (1 : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact h.add_shift_eq_one (by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx)
  have hleft : IntervalIntegrable φ volume (-1) 0 :=
    h.contDiff.continuous.intervalIntegrable _ _
  have hright : IntervalIntegrable φ volume 0 1 :=
    h.contDiff.continuous.intervalIntegrable _ _
  rw [intervalIntegral.integral_add,
    intervalIntegral.integral_comp_sub_right, intervalIntegral.integral_const] at hadd
  · have hjoin := intervalIntegral.integral_add_adjacent_intervals hleft hright
    norm_num at hadd
    linarith
  · exact h.contDiff.continuous.intervalIntegrable _ _
  · exact (h.contDiff.continuous.comp
      (continuous_id.sub continuous_const)).intervalIntegrable _ _

/-- The whole-line integral of an original solution is one.  Compact support
turns this into `intervalIntegral_eq_one`; exposing the whole-line form avoids
repeating that localization in Fourier-transform arguments. -/
theorem integral_eq_one :
    (∫ x : ℝ, φ x) = 1 := by
  have hrestrict : (∫ x : ℝ, φ x) =
      ∫ x : ℝ in Icc (-1 : ℝ) 1, φ x := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · simp [hx]
    · rw [h.eq_zero_of_not_mem hx]
      simp [hx]
  calc
    (∫ x : ℝ, φ x) = ∫ x : ℝ in Icc (-1 : ℝ) 1, φ x := hrestrict
    _ = ∫ x in (-1 : ℝ)..1, φ x := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    _ = 1 := h.intervalIntegral_eq_one

/-- The unspecified constant in the original problem is necessarily `2`. -/
theorem scale_eq_two : k = 2 := by
  have hderiv : ∀ x ∈ uIcc (-1 : ℝ) 0,
      HasDerivAt φ (k * φ (2 * x + 1)) x := by
    intro x hx
    have hx' : x ∈ Icc (-1 : ℝ) 0 := by
      simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] using hx
    have hfar : φ (2 * x - 1) = 0 :=
      h.eq_zero_of_le_neg_one (by linarith [hx'.2])
    simpa [hfar] using h.hasDerivAt x
  have hint : IntervalIntegrable (fun x : ℝ => k * φ (2 * x + 1)) volume (-1) 0 :=
    (h.contDiff.continuous.comp
      ((continuous_const.mul continuous_id).add continuous_const)).const_mul k |>.intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h.value_zero, h.value_neg_one] at hftc
  have hsub : (∫ x in (-1 : ℝ)..0, φ (2 * x + 1)) =
      (1 / 2 : ℝ) * ∫ x in (-1 : ℝ)..1, φ x := by
    have hs := intervalIntegral.integral_comp_mul_add
      (f := φ) (a := (-1 : ℝ)) (b := 0) (c := 2)
        (by norm_num : (2 : ℝ) ≠ 0) 1
    convert hs using 1
    all_goals norm_num
  have hconst : (∫ x in (-1 : ℝ)..0, k * φ (2 * x + 1)) =
      k * ∫ x in (-1 : ℝ)..0, φ (2 * x + 1) := by
    rw [intervalIntegral.integral_const_mul]
  rw [hconst, hsub, h.intervalIntegral_eq_one] at hftc
  linarith

end IsOriginalFabius

/-- Every bounded Fabius solution folds to a solution of Rvachev's original
compact-support characterization, with the forced scale already equal to
two. -/
theorem IsFabius.isOriginalFabius_rvachevUp
    {F : BoundedFabius} (hF : IsFabius F) :
    IsOriginalFabius (rvachevUp F) 2 where
  contDiff := rvachev_contDiff F hF
  tsupport_eq := tsupport_rvachev F hF
  pos_of_mem := fun _x hx => rvachevUp_pos_of_mem_Ioo F hF hx
  value_zero := rvachevUp_zero F hF
  scale_pos := by norm_num
  hasDerivAt := rvachev_hasDerivAt F hF

/-- The canonical Rvachev function supplies the existence half of Theorem 1. -/
theorem canonical_isOriginalFabius :
    IsOriginalFabius (rvachevUp fabius) 2 :=
  fabius_spec.isOriginalFabius_rvachevUp

/-- The constant in every solution of the original characterization is `2`. -/
theorem originalFabius_scale_eq_two {φ : ℝ → ℝ} {k : ℝ}
    (h : IsOriginalFabius φ k) : k = 2 :=
  h.scale_eq_two

end

end Fabius
