import FabiusFunction.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Differential identities for the Fabius and Rvachev functions

This module derives the global differential equation for Rvachev's compactly
supported `up` function from the bounded Fabius derivative identity and
left-tail vanishing alone.  The proof handles the fold point at zero by gluing
the two one-sided derivatives, then bootstraps the differential equation to
smoothness of every finite order.
It also records the closed constant-tail forms of the Fabius derivative and
the exact midpoint derivative, so endpoint arguments do not need to reopen
the global folded formula.
-/

set_option autoImplicit false

open scoped ContDiff
open Set

namespace Fabius

set_option linter.unusedVariables false in
/-- Backwards-compatible form of `rvachevUp_even` for an `IsFabius` candidate. -/
theorem rvachev_even (F : BoundedFabius) (hF : IsFabius F) :
    Function.Even (rvachevUp F) :=
  rvachevUp_even F

/-- Folding preserves the pointwise range `[0,1]` of a bounded candidate. -/
theorem rvachevUp_mem_unitInterval (F : BoundedFabius) (x : ℝ) :
    rvachevUp F x ∈ Icc (0 : ℝ) 1 :=
  ⟨rvachevUp_nonneg F x, rvachevUp_le_one F x⟩

/-- Rvachev's function vanishes at the right endpoint of its support. -/
theorem rvachevUp_one (F : BoundedFabius) (hF : IsFabius F) :
    rvachevUp F 1 = 0 :=
  rvachevUp_eq_zero_of_one_le F hF le_rfl

/-- Rvachev's function vanishes at the left endpoint of its support. -/
theorem rvachevUp_neg_one (F : BoundedFabius) (hF : IsFabius F) :
    rvachevUp F (-1) = 0 :=
  rvachevUp_eq_zero_of_le_neg_one F hF le_rfl

/-- The bounded Fabius function has a vanishing derivative at the right
endpoint of the unit interval, where it attains its global maximum. -/
theorem fabius_hasDerivAt_one (F : BoundedFabius) (hF : IsFabius F) :
    HasDerivAt (fabiusReal F) (0 : ℝ) (1 : ℝ) := by
  have hmax : IsMaxOn (fabiusReal F) Set.univ 1 := by
    intro y _hy
    rw [hF.one_of_one_le 1 le_rfl]
    exact fabiusReal_le_one F y
  have hderiv : deriv (fabiusReal F) 1 = 0 :=
    (hmax.isLocalMax Filter.univ_mem).deriv_eq_zero
  have hd := (hF.contDiff.differentiable (by simp) 1).hasDerivAt
  rwa [hderiv] at hd

private lemma fabius_hasDerivAt_secondHalf_aux (F : BoundedFabius)
    (hF : IsFabius F) {t : ℝ} (htlow : 1 / 2 < t) (hthigh : t < 1) :
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
  convert hs using 1
  ring_nf

/-- To the left of the unit interval the bounded Fabius function is locally
constant, hence has vanishing derivative. -/
theorem fabius_hasDerivAt_of_neg (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x < 0) : HasDerivAt (fabiusReal F) 0 x := by
  apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact hF.zero_of_nonpos y (le_of_lt hy)

/-- To the right of the unit interval the bounded Fabius function is locally
constant, hence has vanishing derivative. -/
theorem fabius_hasDerivAt_of_one_lt (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : 1 < x) : HasDerivAt (fabiusReal F) 0 x := by
  apply (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact hF.one_of_one_le y (le_of_lt hy)

/--
The bounded Fabius function satisfies one differential equation on all of `ℝ`:
`F'(x) = 2 up(2x - 1)`.

On `[0, 1/2]` this is the defining equation `F'(x) = 2 F(2x)`, on `[1/2, 1]` it
is its reflection `F'(x) = 2 F(2 - 2x)`, and outside `[0, 1]` both sides
vanish.  Folding the three cases into a single identity removes the case
analysis from every later derivative computation.
-/
theorem fabius_hasDerivAt (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    HasDerivAt (fabiusReal F) (2 * rvachevUp F (2 * x - 1)) x := by
  by_cases hx0 : 0 ≤ x
  · by_cases hxhalf : x ≤ 1 / 2
    · have h := hF.hasDerivAt x ⟨hx0, hxhalf⟩
      rwa [rvachevUp_of_nonpos F (show 2 * x - 1 ≤ 0 by linarith),
        show 2 * x - 1 + 1 = 2 * x by ring]
    · have hhalf : 1 / 2 < x := lt_of_not_ge hxhalf
      rcases lt_trichotomy x 1 with hx1 | hx1 | hx1
      · have h := fabius_hasDerivAt_secondHalf_aux F hF hhalf hx1
        rwa [rvachevUp_of_pos F (show (0 : ℝ) < 2 * x - 1 by linarith),
          show 1 - (2 * x - 1) = 2 - 2 * x by ring]
      · subst hx1
        rw [show 2 * (1 : ℝ) - 1 = 1 by norm_num, rvachevUp_one F hF, mul_zero]
        exact fabius_hasDerivAt_one F hF
      · rw [rvachevUp_eq_zero_of_one_le F hF (by linarith), mul_zero]
        exact fabius_hasDerivAt_of_one_lt F hF hx1
  · have hx : x < 0 := lt_of_not_ge hx0
    rw [rvachevUp_eq_zero_of_le_neg_one F hF (by linarith), mul_zero]
    exact fabius_hasDerivAt_of_neg F hF hx

/-- On the whole closed left tail `(-∞, 0]`, including the gluing point, the
bounded Fabius function has derivative zero. -/
theorem fabius_hasDerivAt_of_nonpos (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x ≤ 0) : HasDerivAt (fabiusReal F) 0 x := by
  have h := fabius_hasDerivAt F hF x
  have hup : rvachevUp F (2 * x - 1) = 0 :=
    rvachevUp_eq_zero_of_le_neg_one F hF (by linarith)
  simpa [hup] using h

/-- On the whole closed right tail `[1, ∞)`, including the gluing point, the
bounded Fabius function has derivative zero. -/
theorem fabius_hasDerivAt_of_one_le (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : 1 ≤ x) : HasDerivAt (fabiusReal F) 0 x := by
  have h := fabius_hasDerivAt F hF x
  have hup : rvachevUp F (2 * x - 1) = 0 :=
    rvachevUp_eq_zero_of_one_le F hF (by linarith)
  simpa [hup] using h

/-- Exact derivative at the left endpoint of the unit interval. -/
theorem fabius_hasDerivAt_zero (F : BoundedFabius) (hF : IsFabius F) :
    HasDerivAt (fabiusReal F) 0 0 :=
  fabius_hasDerivAt_of_nonpos F hF le_rfl

/-- The derivative reaches its exact maximum `2` at the midpoint. -/
theorem fabius_hasDerivAt_half (F : BoundedFabius) (hF : IsFabius F) :
    HasDerivAt (fabiusReal F) 2 (1 / 2) := by
  have h := fabius_hasDerivAt F hF (1 / 2)
  have harg : 2 * (1 / 2 : ℝ) - 1 = 0 := by norm_num
  simpa [harg, rvachevUp_zero F hF] using h

set_option linter.unusedVariables false in
/--
Reflected form of the defining differential equation on the whole second half
of the unit interval, endpoints included.
-/
theorem fabius_hasDerivAt_secondHalf (F : BoundedFabius) (hF : IsFabius F)
    {t : ℝ} (htlow : 1 / 2 ≤ t) (hthigh : t ≤ 1) :
    HasDerivAt (fabiusReal F) (2 * fabiusReal F (2 - 2 * t)) t := by
  have h := fabius_hasDerivAt F hF t
  have hup : rvachevUp F (2 * t - 1) = fabiusReal F (2 - 2 * t) := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ 2 * t - 1 by linarith) with h0 | h0
    · rw [← h0, rvachevUp_zero F hF, show (2 : ℝ) - 2 * t = 1 by linarith]
      exact (hF.one_of_one_le 1 le_rfl).symm
    · rw [rvachevUp_of_pos F h0]
      congr 1
      ring
  rwa [hup] at h

/-- Closed form for the derivative of the bounded Fabius function. -/
theorem deriv_fabiusReal (F : BoundedFabius) (hF : IsFabius F) :
    deriv (fabiusReal F) = fun x : ℝ => 2 * rvachevUp F (2 * x - 1) := by
  funext x
  exact (fabius_hasDerivAt F hF x).deriv

/-- The bounded Fabius function is differentiable on all of `ℝ`. -/
theorem fabius_differentiable (F : BoundedFabius) (hF : IsFabius F) :
    Differentiable ℝ (fabiusReal F) :=
  fun x => (fabius_hasDerivAt F hF x).differentiableAt

private lemma rvachevUp_left_hasDerivAt_of_hasDerivAt (F : BoundedFabius)
    (hderiv : ∀ x : ℝ,
      HasDerivAt (fabiusReal F) (2 * rvachevUp F (2 * x - 1)) x)
    {x : ℝ} :
    HasDerivAt (fun y : ℝ => fabiusReal F (y + 1))
      (2 * rvachevUp F (2 * x + 1)) x := by
  have h := (hderiv (x + 1)).comp_add_const x 1
  rw [show 2 * (x + 1) - 1 = 2 * x + 1 by ring] at h
  exact h

private lemma rvachevUp_hasDerivAt_of_neg_of_hasDerivAt (F : BoundedFabius)
    (hderiv : ∀ x : ℝ,
      HasDerivAt (fabiusReal F) (2 * rvachevUp F (2 * x - 1)) x)
    {x : ℝ} (hx : x < 0) :
    HasDerivAt (rvachevUp F) (2 * rvachevUp F (2 * x + 1)) x := by
  have hl := rvachevUp_left_hasDerivAt_of_hasDerivAt F hderiv (x := x)
  apply hl.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with y hy
  have hyle : y ≤ 0 := le_of_lt hy
  simp [rvachevUp, hyle]

/-- Rvachev's refinement equation follows from the global bounded-Fabius
derivative identity together with vanishing on the left tail; no smoothness,
symmetry, or fixed-point information is needed. -/
theorem rvachevUp_hasDerivAt_of_fabiusReal_hasDerivAt
    (F : BoundedFabius)
    (hzero : ∀ x : ℝ, x ≤ 0 → fabiusReal F x = 0)
    (hderiv : ∀ x : ℝ,
      HasDerivAt (fabiusReal F) (2 * rvachevUp F (2 * x - 1)) x)
    (x : ℝ) :
    HasDerivAt (rvachevUp F)
      (2 * (rvachevUp F (2 * x + 1) - rvachevUp F (2 * x - 1))) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hmain := rvachevUp_hasDerivAt_of_neg_of_hasDerivAt F hderiv hx
    have hsecond : rvachevUp F (2 * x - 1) = 0 := by
      rw [rvachevUp, if_pos (by linarith), hzero _ (by linarith)]
    rw [hsecond]
    simpa using hmain
  · have hupOne : rvachevUp F 1 = 0 := by
      rw [rvachevUp, if_neg (by norm_num), show (1 : ℝ) - 1 = 0 by norm_num]
      exact hzero 0 le_rfl
    have hupNegOne : rvachevUp F (-1) = 0 := by
      rw [rvachevUp, if_pos (by norm_num), show (-1 : ℝ) + 1 = 0 by norm_num]
      exact hzero 0 le_rfl
    have hl0 := rvachevUp_left_hasDerivAt_of_hasDerivAt F hderiv (x := 0)
    have hcoef : 2 * rvachevUp F (2 * (0 : ℝ) + 1) = 0 := by
      norm_num [hupOne]
    rw [hcoef] at hl0
    have hl : HasDerivWithinAt (rvachevUp F) 0 (Iic (0 : ℝ)) 0 := by
      have h : HasDerivWithinAt (fun y : ℝ => fabiusReal F (y + 1)) 0
          (Iic (0 : ℝ)) 0 := hl0.hasDerivWithinAt
      refine h.congr_of_mem ?_ (by simp)
      intro y hy
      change y ≤ 0 at hy
      rw [rvachevUp, if_pos hy]
    have hone : HasDerivAt (fabiusReal F) 0 1 := by
      have h := hderiv 1
      rw [show 2 * (1 : ℝ) - 1 = 1 by norm_num, hupOne, mul_zero] at h
      exact h
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
    simpa [hupOne, hupNegOne] using hu
  · have hneg := rvachevUp_hasDerivAt_of_neg_of_hasDerivAt F hderiv
      (show -x < 0 by linarith)
    have hneg' : HasDerivAt (rvachevUp F)
        (2 * rvachevUp F (2 * (-x) + 1)) ((0 : ℝ) - x) := by simpa using hneg
    have hcomp := hneg'.comp_const_sub 0 x
    have hup : HasDerivAt (rvachevUp F)
        (-(2 * rvachevUp F (2 * (-x) + 1))) x := by
      apply hcomp.congr_of_eventuallyEq
      filter_upwards with y
      simpa using (rvachevUp_even F y).symm
    convert hup using 1
    · have hfar : rvachevUp F (2 * x + 1) = 0 := by
        rw [rvachevUp, if_neg (by linarith), hzero _ (by linarith)]
      rw [hfar]
      have heven := rvachevUp_even F (2 * x - 1)
      have heq : rvachevUp F (2 * (-x) + 1) = rvachevUp F (2 * x - 1) := by
        convert heven using 1
        ring_nf
      rw [heq]
      ring

/-- The differential equation defining Rvachev's function. -/
theorem rvachev_hasDerivAt (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    HasDerivAt (rvachevUp F)
      (2 * (rvachevUp F (2 * x + 1) - rvachevUp F (2 * x - 1))) x :=
  rvachevUp_hasDerivAt_of_fabiusReal_hasDerivAt F hF.zero_of_nonpos
    (fabius_hasDerivAt F hF) x

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
