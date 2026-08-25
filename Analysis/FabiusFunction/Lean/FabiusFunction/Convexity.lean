import FabiusFunction.Monotonicity
import Mathlib.Analysis.Convex.Deriv

/-!
# Convexity of the Fabius function on the two halves of its interval

The unified differential equation `F'(x) = 2 up(2x - 1)` turns the shape of
`up` into the second-order shape of `F`.  Rvachev's function increases on
`[-1,0]` and decreases on `[0,1]`, and `x ↦ 2x - 1` maps `(-∞, 1/2]` into
`(-∞, 0]` and `[1/2, ∞)` into `[0, ∞)`.  Hence `F'` is monotone on the left
half line and antitone on the right one, so `F` is convex on `(-∞, 1/2]` and
concave on `[1/2, ∞)`, with strict convexity and concavity on the two halves
of the unit interval, where the monotonicity of `up` is strict.

The inflection point is therefore exactly the midpoint, where `F(1/2) = 1/2`
and `F'(1/2) = 2` is the unique global maximum of the derivative.  The exact
range statement is recorded below: `0 ≤ F'(x) ≤ 2`, with equality on the
left exactly off `(0,1)` and equality on the right exactly at `x = 1/2`.
-/

set_option autoImplicit false

open scoped ContDiff
open Set

namespace Fabius

/-! ## Global one-sided monotonicity of Rvachev's function -/

/-- Rvachev's function is monotone on the whole nonpositive half line. -/
theorem monotoneOn_rvachevUp_Iic (F : BoundedFabius) (hF : IsFabius F) :
    MonotoneOn (rvachevUp F) (Iic (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx0 : x ≤ 0 := hx
  have hy0 : y ≤ 0 := hy
  by_cases hx1 : x ≤ -1
  · rw [rvachevUp_eq_zero_of_le_neg_one F hF hx1]
    exact rvachevUp_nonneg F y
  · have hxm : x ∈ Icc (-1 : ℝ) 0 := ⟨le_of_lt (lt_of_not_ge hx1), hx0⟩
    have hym : y ∈ Icc (-1 : ℝ) 0 := ⟨by linarith [hxm.1], hy0⟩
    rcases eq_or_lt_of_le hxy with h | h
    · rw [h]
    · exact le_of_lt (strictMonoOn_rvachevUp F hF hxm hym h)

/-- Rvachev's function is antitone on the whole nonnegative half line. -/
theorem antitoneOn_rvachevUp_Ici (F : BoundedFabius) (hF : IsFabius F) :
    AntitoneOn (rvachevUp F) (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  by_cases hy1 : 1 ≤ y
  · rw [rvachevUp_eq_zero_of_one_le F hF hy1]
    exact rvachevUp_nonneg F x
  · have hym : y ∈ Icc (0 : ℝ) 1 := ⟨hy0, le_of_lt (lt_of_not_ge hy1)⟩
    have hxm : x ∈ Icc (0 : ℝ) 1 := ⟨hx0, by linarith [hym.2]⟩
    rcases eq_or_lt_of_le hxy with h | h
    · rw [h]
    · exact le_of_lt (strictAntiOn_rvachevUp F hF hxm hym h)

/-! ## Monotonicity of the derivative -/

/-- The derivative of the bounded Fabius function is monotone to the left of
the midpoint. -/
theorem monotoneOn_deriv_fabiusReal (F : BoundedFabius) (hF : IsFabius F) :
    MonotoneOn (deriv (fabiusReal F)) (Iic (1 / 2 : ℝ)) := by
  intro x hx y hy hxy
  have hx' : x ≤ 1 / 2 := hx
  have hy' : y ≤ 1 / 2 := hy
  rw [(fabius_hasDerivAt F hF x).deriv, (fabius_hasDerivAt F hF y).deriv]
  have h := monotoneOn_rvachevUp_Iic F hF
    (show 2 * x - 1 ∈ Iic (0 : ℝ) from by
      have : 2 * x - 1 ≤ 0 := by linarith
      exact this)
    (show 2 * y - 1 ∈ Iic (0 : ℝ) from by
      have : 2 * y - 1 ≤ 0 := by linarith
      exact this)
    (by linarith)
  linarith

/-- The derivative of the bounded Fabius function is antitone to the right of
the midpoint. -/
theorem antitoneOn_deriv_fabiusReal (F : BoundedFabius) (hF : IsFabius F) :
    AntitoneOn (deriv (fabiusReal F)) (Ici (1 / 2 : ℝ)) := by
  intro x hx y hy hxy
  have hx' : 1 / 2 ≤ x := hx
  have hy' : 1 / 2 ≤ y := hy
  rw [(fabius_hasDerivAt F hF x).deriv, (fabius_hasDerivAt F hF y).deriv]
  have h := antitoneOn_rvachevUp_Ici F hF
    (show 2 * x - 1 ∈ Ici (0 : ℝ) from by
      have : (0 : ℝ) ≤ 2 * x - 1 := by linarith
      exact this)
    (show 2 * y - 1 ∈ Ici (0 : ℝ) from by
      have : (0 : ℝ) ≤ 2 * y - 1 := by linarith
      exact this)
    (by linarith)
  linarith

/-! ## Exact range of the derivative -/

/-- The derivative of the bounded Fabius function is nonnegative everywhere. -/
theorem deriv_fabiusReal_nonneg (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    0 ≤ deriv (fabiusReal F) x := by
  rw [(fabius_hasDerivAt F hF x).deriv]
  exact mul_nonneg (by norm_num) (rvachevUp_nonneg F (2 * x - 1))

/-- The derivative of the bounded Fabius function is at most two everywhere. -/
theorem deriv_fabiusReal_le_two (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    deriv (fabiusReal F) x ≤ 2 := by
  rw [(fabius_hasDerivAt F hF x).deriv]
  nlinarith [rvachevUp_le_one F (2 * x - 1)]

/-- The derivative of the bounded Fabius function takes values in `[0,2]`. -/
theorem deriv_fabiusReal_mem_Icc (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    deriv (fabiusReal F) x ∈ Icc (0 : ℝ) 2 :=
  ⟨deriv_fabiusReal_nonneg F hF x, deriv_fabiusReal_le_two F hF x⟩

/-- At the midpoint the derivative of the bounded Fabius function is two. -/
theorem deriv_fabiusReal_half (F : BoundedFabius) (hF : IsFabius F) :
    deriv (fabiusReal F) (1 / 2 : ℝ) = 2 := by
  rw [(fabius_hasDerivAt F hF (1 / 2 : ℝ)).deriv,
    show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num, rvachevUp_zero F hF]
  norm_num

/-- The derivative vanishes exactly outside the open unit interval, including
at both endpoints. -/
theorem deriv_fabiusReal_eq_zero_iff (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) :
    deriv (fabiusReal F) x = 0 ↔ x ∉ Ioo (0 : ℝ) 1 := by
  constructor
  · intro hx hmem
    exact (deriv_fabiusReal_pos F hF hmem).ne' hx
  · intro hx
    have harg : 2 * x - 1 ∉ Ioo (-1 : ℝ) 1 := by
      intro hmem
      apply hx
      exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
    rw [(fabius_hasDerivAt F hF x).deriv,
      rvachevUp_eq_zero_of_not_mem_Ioo F hF harg, mul_zero]

/-- The derivative reaches two only at the midpoint. -/
theorem deriv_fabiusReal_eq_two_iff (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) :
    deriv (fabiusReal F) x = 2 ↔ x = 1 / 2 := by
  rw [(fabius_hasDerivAt F hF x).deriv]
  constructor
  · intro hx
    have hup : rvachevUp F (2 * x - 1) = 1 := by linarith
    have harg := (rvachevUp_eq_one_iff F hF (2 * x - 1)).mp hup
    linarith
  · rintro rfl
    rw [show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num, rvachevUp_zero F hF]
    norm_num

/-- Two is the maximum value of the derivative, and it is attained uniquely
at the midpoint by `deriv_fabiusReal_eq_two_iff`. -/
theorem isGreatest_deriv_fabiusReal (F : BoundedFabius) (hF : IsFabius F) :
    IsGreatest (Set.range fun x : ℝ => deriv (fabiusReal F) x) 2 := by
  constructor
  · exact ⟨(1 / 2 : ℝ), deriv_fabiusReal_half F hF⟩
  · rintro y ⟨x, rfl⟩
    exact deriv_fabiusReal_le_two F hF x

/--
On the *closed* first half `[0, 1/2]` the derivative is strictly increasing.

This is the sharp form of `strictMonoOn_deriv_fabiusReal`, which states the
same conclusion on the open interval only.  Nothing extra is needed for the
endpoints: the argument factors through `strictMonoOn_rvachevUp`, which is
itself stated on the *closed* interval `[-1, 0]`, and `x ↦ 2 * x - 1` maps
`[0, 1/2]` onto exactly `[-1, 0]`.

The endpoints carry real content: together with `F' 0 = 0` and `F' (1/2) = 2`
this gives the strict two-sided bound `0 < F' x < 2` for `0 < x < 1/2`, and it
makes `deriv (fabiusReal F)` injective on the closed half.
-/
theorem strictMonoOn_deriv_fabiusReal_Icc (F : BoundedFabius) (hF : IsFabius F) :
    StrictMonoOn (deriv (fabiusReal F)) (Icc (0 : ℝ) (1 / 2)) := by
  intro x hx y hy hxy
  rw [(fabius_hasDerivAt F hF x).deriv, (fabius_hasDerivAt F hF y).deriv]
  have h := strictMonoOn_rvachevUp F hF
    (show 2 * x - 1 ∈ Icc (-1 : ℝ) 0 from ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    (show 2 * y - 1 ∈ Icc (-1 : ℝ) 0 from ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    (by linarith)
  linarith

/--
On the *closed* second half `[1/2, 1]` the derivative is strictly decreasing.

This is the sharp form of `strictAntiOn_deriv_fabiusReal`, which states the
same conclusion on the open interval only.  As above the endpoints come for
free: `strictAntiOn_rvachevUp` is stated on the closed interval `[0, 1]` and
`x ↦ 2 * x - 1` maps `[1/2, 1]` onto exactly `[0, 1]`.
-/
theorem strictAntiOn_deriv_fabiusReal_Icc (F : BoundedFabius) (hF : IsFabius F) :
    StrictAntiOn (deriv (fabiusReal F)) (Icc (1 / 2 : ℝ) 1) := by
  intro x hx y hy hxy
  rw [(fabius_hasDerivAt F hF x).deriv, (fabius_hasDerivAt F hF y).deriv]
  have h := strictAntiOn_rvachevUp F hF
    (show 2 * x - 1 ∈ Icc (0 : ℝ) 1 from ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    (show 2 * y - 1 ∈ Icc (0 : ℝ) 1 from ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    (by linarith)
  linarith

/-- On the interior of the first half the derivative is strictly increasing. -/
theorem strictMonoOn_deriv_fabiusReal (F : BoundedFabius) (hF : IsFabius F) :
    StrictMonoOn (deriv (fabiusReal F)) (Ioo (0 : ℝ) (1 / 2)) := by
  exact (strictMonoOn_deriv_fabiusReal_Icc F hF).mono Ioo_subset_Icc_self

/-- On the interior of the second half the derivative is strictly decreasing. -/
theorem strictAntiOn_deriv_fabiusReal (F : BoundedFabius) (hF : IsFabius F) :
    StrictAntiOn (deriv (fabiusReal F)) (Ioo (1 / 2 : ℝ) 1) := by
  exact (strictAntiOn_deriv_fabiusReal_Icc F hF).mono Ioo_subset_Icc_self

/-! ## Convexity and concavity -/

/-- The bounded Fabius function is convex on `(-∞, 1/2]`. -/
theorem convexOn_fabiusReal_Iic_half (F : BoundedFabius) (hF : IsFabius F) :
    ConvexOn ℝ (Iic (1 / 2 : ℝ)) (fabiusReal F) := by
  have hmono : MonotoneOn (deriv (fabiusReal F))
      (interior (Iic (1 / 2 : ℝ))) := by
    rw [interior_Iic]
    exact (monotoneOn_deriv_fabiusReal F hF).mono Iio_subset_Iic_self
  exact hmono.convexOn_of_deriv (convex_Iic _)
    hF.contDiff.continuous.continuousOn
    (fabius_differentiable F hF).differentiableOn

/-- The bounded Fabius function is concave on `[1/2, ∞)`. -/
theorem concaveOn_fabiusReal_Ici_half (F : BoundedFabius) (hF : IsFabius F) :
    ConcaveOn ℝ (Ici (1 / 2 : ℝ)) (fabiusReal F) := by
  have hanti : AntitoneOn (deriv (fabiusReal F))
      (interior (Ici (1 / 2 : ℝ))) := by
    rw [interior_Ici]
    exact (antitoneOn_deriv_fabiusReal F hF).mono Ioi_subset_Ici_self
  exact hanti.concaveOn_of_deriv (convex_Ici _)
    hF.contDiff.continuous.continuousOn
    (fabius_differentiable F hF).differentiableOn

/--
The bounded Fabius function is strictly convex on `[0, 1/2]`.

The interval cannot be enlarged to `(-∞, 1/2]`: the function is constant to
the left of the origin, so strict convexity fails there.
-/
theorem strictConvexOn_fabiusReal_firstHalf (F : BoundedFabius) (hF : IsFabius F) :
    StrictConvexOn ℝ (Icc (0 : ℝ) (1 / 2)) (fabiusReal F) := by
  have hmono : StrictMonoOn (deriv (fabiusReal F))
      (interior (Icc (0 : ℝ) (1 / 2))) := by
    rw [interior_Icc]
    exact strictMonoOn_deriv_fabiusReal F hF
  exact hmono.strictConvexOn_of_deriv (convex_Icc _ _)
    hF.contDiff.continuous.continuousOn

/--
The bounded Fabius function is strictly concave on `[1/2, 1]`.

The interval cannot be enlarged to `[1/2, ∞)`: the function is constant to
the right of one, so strict concavity fails there.
-/
theorem strictConcaveOn_fabiusReal_secondHalf (F : BoundedFabius) (hF : IsFabius F) :
    StrictConcaveOn ℝ (Icc (1 / 2 : ℝ) 1) (fabiusReal F) := by
  have hanti : StrictAntiOn (deriv (fabiusReal F))
      (interior (Icc (1 / 2 : ℝ) 1)) := by
    rw [interior_Icc]
    exact strictAntiOn_deriv_fabiusReal F hF
  exact hanti.strictConcaveOn_of_deriv (convex_Icc _ _)
    hF.contDiff.continuous.continuousOn

end Fabius
