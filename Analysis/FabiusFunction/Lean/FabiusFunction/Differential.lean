import FabiusFunction.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Differential identities for the Fabius and Rvachev functions

This module derives the global differential equation for Rvachev's compactly
supported `up` function from the bounded Fabius characterization.  The proof
handles the fold point at zero by gluing the two one-sided derivatives, then
bootstraps the differential equation to smoothness of every finite order.
-/

set_option autoImplicit false

open scoped ContDiff
open Set

namespace Fabius

/-- Folding a bounded candidate about zero always produces an even function.
No Fabius equations are needed for this structural fact. -/
theorem rvachevUp_even (F : BoundedFabius) :
    Function.Even (rvachevUp F) := by
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  by_cases hxpos : 0 < x
  · have hnx : -x ≤ 0 := by linarith
    have hxnot : ¬ x ≤ 0 := not_le.mpr hxpos
    simp only [rvachevUp, if_pos hnx, if_neg hxnot]
    congr 1
    ring
  · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx
    have hnxnot : ¬ -x ≤ 0 := by linarith
    have hxle : x ≤ 0 := hxneg.le
    simp only [rvachevUp, if_neg hnxnot, if_pos hxle]
    congr 1
    ring

/-- Backwards-compatible form of `rvachevUp_even` for an `IsFabius` candidate. -/
theorem rvachev_even (F : BoundedFabius) (_hF : IsFabius F) :
    Function.Even (rvachevUp F) :=
  rvachevUp_even F

/-- Rvachev's folded function vanishes at and to the left of `-1`. -/
theorem rvachevUp_eq_zero_of_le_neg_one (F : BoundedFabius)
    (hF : IsFabius F) {x : ℝ} (hx : x ≤ -1) : rvachevUp F x = 0 := by
  rw [rvachevUp, if_pos (by linarith), hF.zero_of_nonpos _ (by linarith)]

/-- Rvachev's folded function vanishes at and to the right of `1`. -/
theorem rvachevUp_eq_zero_of_one_le (F : BoundedFabius)
    (hF : IsFabius F) {x : ℝ} (hx : 1 ≤ x) : rvachevUp F x = 0 := by
  rw [rvachevUp, if_neg (by linarith), hF.zero_of_nonpos _ (by linarith)]

/-- A point outside the open support interval is a zero of Rvachev's function. -/
theorem rvachevUp_eq_zero_of_not_mem_Ioo (F : BoundedFabius)
    (hF : IsFabius F) {x : ℝ} (hx : x ∉ Ioo (-1 : ℝ) 1) :
    rvachevUp F x = 0 := by
  by_cases hleft : x ≤ -1
  · exact rvachevUp_eq_zero_of_le_neg_one F hF hleft
  · apply rvachevUp_eq_zero_of_one_le F hF
    have hxinside : -1 < x := lt_of_not_ge hleft
    by_contra hright
    exact hx ⟨hxinside, lt_of_not_ge hright⟩

/-- Folding preserves the pointwise range `[0,1]` of a bounded candidate. -/
theorem rvachevUp_mem_unitInterval (F : BoundedFabius) (x : ℝ) :
    rvachevUp F x ∈ Icc (0 : ℝ) 1 := by
  unfold rvachevUp
  split_ifs <;> exact ⟨fabiusReal_nonneg F _, fabiusReal_le_one F _⟩

/-- Rvachev's folded function is nonnegative, without any Fabius equations. -/
theorem rvachevUp_nonneg (F : BoundedFabius) (x : ℝ) :
    0 ≤ rvachevUp F x :=
  (rvachevUp_mem_unitInterval F x).1

/-- Rvachev's folded function is at most one, without any Fabius equations. -/
theorem rvachevUp_le_one (F : BoundedFabius) (x : ℝ) :
    rvachevUp F x ≤ 1 :=
  (rvachevUp_mem_unitInterval F x).2

/-- Absolute values may be removed from the nonnegative folded function. -/
@[simp]
theorem abs_rvachevUp (F : BoundedFabius) (x : ℝ) :
    |rvachevUp F x| = rvachevUp F x :=
  abs_of_nonneg (rvachevUp_nonneg F x)

/-- The folded function is bounded by one in absolute value. -/
theorem abs_rvachevUp_le_one (F : BoundedFabius) (x : ℝ) :
    |rvachevUp F x| ≤ 1 := by
  rw [abs_rvachevUp]
  exact rvachevUp_le_one F x

/-- The folded function is bounded by one in the real norm. -/
theorem norm_rvachevUp_le_one (F : BoundedFabius) (x : ℝ) :
    ‖rvachevUp F x‖ ≤ 1 := by
  simpa [Real.norm_eq_abs] using abs_rvachevUp_le_one F x

/-- The complex coercion of the folded function is bounded by one in norm. -/
theorem norm_coe_rvachevUp_le_one (F : BoundedFabius) (x : ℝ) :
    ‖(rvachevUp F x : ℂ)‖ ≤ 1 := by
  simpa [Complex.norm_real, Real.norm_eq_abs] using abs_rvachevUp_le_one F x

private lemma fabius_hasDerivAt_one (F : BoundedFabius) (hF : IsFabius F) :
    HasDerivAt (fabiusReal F) (0 : ℝ) (1 : ℝ) := by
  have hmax : IsMaxOn (fabiusReal F) Set.univ 1 := by
    intro y _hy
    rw [hF.one_of_one_le 1 le_rfl]
    exact fabiusReal_le_one F y
  have hderiv : deriv (fabiusReal F) 1 = 0 :=
    (hmax.isLocalMax Filter.univ_mem).deriv_eq_zero
  have hd := (hF.contDiff.differentiable (by simp) 1).hasDerivAt
  rwa [hderiv] at hd

private lemma fabius_hasDerivAt_high (F : BoundedFabius) (hF : IsFabius F)
    {t : ℝ} (htlow : 1 / 2 < t) (hthigh : t < 1) :
    HasDerivAt (fabiusReal F) (2 * fabiusReal F (2 - 2 * t)) t := by
  have harg : 1 - t ∈ Icc (0 : ℝ) (1 / 2) := by
    constructor <;> linarith
  have hd := hF.hasDerivAt (1 - t) harg
  have hdpoint : HasDerivAt (fabiusReal F)
      (2 * fabiusReal F (2 * (1 - t))) ((1 : ℝ) - t) := by
    simpa using hd
  have hcomp := hdpoint.comp_const_sub 1 t
  have hrhs : HasDerivAt (fun y : ℝ => 1 - fabiusReal F (1 - y))
      (2 * fabiusReal F (2 - 2 * t)) t := by
    have hargEq : 2 * (1 - t) = (2 - 2 * t : ℝ) := by ring
    rw [hargEq] at hcomp
    simpa only [neg_neg] using hcomp.const_sub (1 : ℝ)
  apply hrhs.congr_of_eventuallyEq
  filter_upwards with y
  have hs := hF.symmetry_all (1 - y)
  convert hs using 1 <;> ring

private lemma rvachev_left_hasDerivAt (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x ≤ 0) :
    HasDerivAt (fun y : ℝ => fabiusReal F (y + 1))
      (2 * rvachevUp F (2 * x + 1)) x := by
  rcases lt_trichotomy x (-1) with hxlt | hxeq | hxgt
  · have htlt : x + 1 < 0 := by linarith
    have hzero : HasDerivAt (fabiusReal F) 0 (x + 1) := by
      apply (hasDerivAt_const (x := x + 1) (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds htlt] with y hy
      exact hF.zero_of_nonpos y (le_of_lt hy)
    have hshift : HasDerivAt (fun y : ℝ => fabiusReal F (y + 1)) 0 x := by
      exact hzero.comp_add_const x 1
    have hup : rvachevUp F (2 * x + 1) = 0 := by
      rw [rvachevUp, if_pos (by linarith : 2 * x + 1 ≤ 0),
        hF.zero_of_nonpos _ (by linarith)]
    rw [hup]
    simpa using hshift
  · subst x
    have hd := hF.hasDerivAt 0 (by constructor <;> norm_num)
    have hd0 : HasDerivAt (fabiusReal F) 0 ((-1 : ℝ) + 1) := by
      simpa [hF.zero_of_nonpos 0 le_rfl] using hd
    have hshift := hd0.comp_add_const (-1 : ℝ) 1
    have hup : rvachevUp F (2 * (-1 : ℝ) + 1) = 0 := by
      rw [show 2 * (-1 : ℝ) + 1 = -1 by norm_num, rvachevUp,
        if_pos (by norm_num)]
      simpa using hF.zero_of_nonpos 0 le_rfl
    rw [hup]
    simpa using hshift
  · rcases lt_trichotomy x (-(1 / 2 : ℝ)) with hxhalf | hxhalf | hxhalf
    · have harg : x + 1 ∈ Icc (0 : ℝ) (1 / 2) := by
        constructor <;> linarith
      have hd := hF.hasDerivAt (x + 1) harg
      have hshift := hd.comp_add_const x 1
      have hup : rvachevUp F (2 * x + 1) = fabiusReal F (2 * (x + 1)) := by
        rw [rvachevUp, if_pos (by linarith : 2 * x + 1 ≤ 0)]
        congr 1
        ring
      rw [hup]
      exact hshift
    · subst x
      have harg : (-(1 / 2 : ℝ)) + 1 ∈ Icc (0 : ℝ) (1 / 2) := by
        constructor <;> norm_num
      have hd := hF.hasDerivAt ((-(1 / 2 : ℝ)) + 1) harg
      have hshift := hd.comp_add_const (-(1 / 2 : ℝ)) 1
      have hup : rvachevUp F (2 * (-(1 / 2 : ℝ)) + 1) =
          fabiusReal F (2 * ((-(1 / 2 : ℝ)) + 1)) := by
        rw [rvachevUp, if_pos (by norm_num : 2 * (-(1 / 2 : ℝ)) + 1 ≤ 0)]
        congr 1
        ring
      rw [hup]
      exact hshift
    · rcases eq_or_lt_of_le hx with rfl | hxzero
      · have hd := fabius_hasDerivAt_one F hF
        have hd' : HasDerivAt (fabiusReal F) 0 ((0 : ℝ) + 1) := by simpa using hd
        have hshift := hd'.comp_add_const 0 1
        have hup : rvachevUp F (2 * (0 : ℝ) + 1) = 0 := by
          simp [rvachevUp, hF.zero_of_nonpos]
        rw [hup]
        simpa using hshift
      · have htlow : 1 / 2 < x + 1 := by linarith
        have hthigh : x + 1 < 1 := by linarith
        have hd := fabius_hasDerivAt_high F hF htlow hthigh
        have hshift := hd.comp_add_const x 1
        have hup : rvachevUp F (2 * x + 1) =
            fabiusReal F (2 - 2 * (x + 1)) := by
          rw [rvachevUp, if_neg (by linarith : ¬ 2 * x + 1 ≤ 0)]
          congr 1
          ring
        rw [hup]
        exact hshift

private lemma rvachev_hasDerivAt_of_neg (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x < 0) :
    HasDerivAt (rvachevUp F) (2 * rvachevUp F (2 * x + 1)) x := by
  have hl := rvachev_left_hasDerivAt F hF hx.le
  apply hl.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with y hy
  have hyle : y ≤ 0 := le_of_lt hy
  simp [rvachevUp, hyle]

/-- The differential equation defining Rvachev's function. -/
theorem rvachev_hasDerivAt (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    HasDerivAt (rvachevUp F)
      (2 * (rvachevUp F (2 * x + 1) - rvachevUp F (2 * x - 1))) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hmain := rvachev_hasDerivAt_of_neg F hF hx
    have hsecond : rvachevUp F (2 * x - 1) = 0 := by
      rw [rvachevUp, if_pos (by linarith : 2 * x - 1 ≤ 0),
        hF.zero_of_nonpos _ (by linarith)]
    rw [hsecond]
    simpa using hmain
  · have hl0 := rvachev_left_hasDerivAt F hF (x := 0) le_rfl
    have hcoef : 2 * rvachevUp F (2 * (0 : ℝ) + 1) = 0 := by
      simp [rvachevUp, hF.zero_of_nonpos]
    rw [hcoef] at hl0
    have hl : HasDerivWithinAt (rvachevUp F) 0 (Iic (0 : ℝ)) 0 := by
      have h : HasDerivWithinAt (fun y : ℝ => fabiusReal F (y + 1)) 0
          (Iic (0 : ℝ)) 0 := hl0.hasDerivWithinAt
      refine h.congr_of_mem ?_ (by simp)
      intro y hy
      change y ≤ 0 at hy
      rw [rvachevUp, if_pos hy]
    have hone := fabius_hasDerivAt_one F hF
    have hone' : HasDerivAt (fabiusReal F) 0 ((1 : ℝ) - 0) := by simpa using hone
    have hr0 := hone'.comp_const_sub 1 (0 : ℝ)
    have hr : HasDerivWithinAt (rvachevUp F) 0 (Ici (0 : ℝ)) 0 := by
      have h : HasDerivWithinAt (fun y : ℝ => fabiusReal F (1 - y)) 0
          (Ici (0 : ℝ)) 0 := by simpa using hr0.hasDerivWithinAt
      refine h.congr_of_mem ?_ (by simp)
      intro y hy
      by_cases hy0 : y = 0
      · subst y
        simp [rvachevUp]
      · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
        simp [rvachevUp, not_le.mpr hypos]
    have hu := hl.union hr
    rw [Iic_union_Ici] at hu
    have hzero : rvachevUp F 1 = 0 := by
      simp [rvachevUp, hF.zero_of_nonpos]
    have hnegone : rvachevUp F (-1) = 0 := by
      simp [rvachevUp, hF.zero_of_nonpos]
    simpa [hzero, hnegone] using hu
  · have hneg := rvachev_hasDerivAt_of_neg F hF (show -x < 0 by linarith)
    have hneg' : HasDerivAt (rvachevUp F)
        (2 * rvachevUp F (2 * (-x) + 1)) ((0 : ℝ) - x) := by simpa using hneg
    have hcomp := hneg'.comp_const_sub 0 x
    have hup : HasDerivAt (rvachevUp F)
        (-(2 * rvachevUp F (2 * (-x) + 1))) x := by
      apply hcomp.congr_of_eventuallyEq
      filter_upwards with y
      simpa using (rvachev_even F hF y).symm
    convert hup using 1
    · have hfar : rvachevUp F (2 * x + 1) = 0 := by
        rw [rvachevUp, if_neg (by linarith), hF.zero_of_nonpos _ (by linarith)]
      rw [hfar]
      have heven := rvachev_even F hF (2 * x - 1)
      have heq : rvachevUp F (2 * (-x) + 1) = rvachevUp F (2 * x - 1) := by
        convert heven using 1 <;> ring
      rw [heq]
      ring

/-- Pointwise derivative form of Rvachev's differential equation. -/
theorem deriv_rvachevUp (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    deriv (rvachevUp F) x =
      2 * (rvachevUp F (2 * x + 1) - rvachevUp F (2 * x - 1)) :=
  (rvachev_hasDerivAt F hF x).deriv

/-- Any solution of Rvachev's dyadic differential refinement equation is smooth.

This isolates the regularity bootstrap from the construction and from the
particular folded representation of the canonical solution. -/
theorem contDiff_of_hasDerivAt_dyadic_refinement (u : ℝ → ℝ)
    (hu : ∀ x : ℝ, HasDerivAt u (2 * (u (2 * x + 1) - u (2 * x - 1))) x) :
    ContDiff ℝ ∞ u := by
  have hdifferentiable : Differentiable ℝ u :=
    fun x => (hu x).differentiableAt
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hdifferentiable.continuous
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
        contDiff_succ_iff_deriv]
      refine ⟨hdifferentiable, by simp, ?_⟩
      have hderiv : deriv u = fun x : ℝ =>
          2 * (u (2 * x + 1) - u (2 * x - 1)) := by
        funext x
        exact (hu x).deriv
      rw [hderiv]
      have hplus : ContDiff ℝ n (fun x : ℝ => u (2 * x + 1)) :=
        ih.comp ((contDiff_const.mul contDiff_id).add contDiff_const)
      have hminus : ContDiff ℝ n (fun x : ℝ => u (2 * x - 1)) :=
        ih.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
      exact contDiff_const.mul (hplus.sub hminus)

/-- Rvachev's function is smooth. -/
theorem rvachev_contDiff (F : BoundedFabius) (hF : IsFabius F) :
    ContDiff ℝ ∞ (rvachevUp F) :=
  contDiff_of_hasDerivAt_dyadic_refinement _ (rvachev_hasDerivAt F hF)

end Fabius
