import FabiusFunction.Differential
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# Monotonicity, positivity, support, and strict monotonicity

This module collects the order-theoretic consequences of the defining
differential equation.  The monotonicity, positivity, and support statements
used to live inside `FabiusFunction.PaperStatements`, which forced every
consumer of a purely order-theoretic fact to import the whole
arXiv:1702.06487v3 index file.  They are foundational, they need nothing
beyond `FabiusFunction.Differential`, and they are collected here instead.

The new content is the strict theory.  The unified derivative formula
`F'(x) = 2 up(2x - 1)` of `FabiusFunction.Differential` is strictly positive
exactly on `(0,1)`, because `up` is strictly positive exactly on `(-1,1)`.
Consequently:

* `F` is strictly increasing on `[0,1]`, hence injective there, and the
  intermediate value theorem upgrades this to a bijection of `[0,1]` onto
  itself;
* the support of `up` is exactly `(-1,1)`, not merely contained in `[-1,1]`;
* `up` is strictly increasing on `[-1,0]`, strictly decreasing on `[0,1]`, and
  attains its maximum `1` only at the origin.

The positivity and one-sided statements are also upgraded to `iff` form.
-/

set_option autoImplicit false

open scoped ContDiff
open Set

namespace Fabius

/-! ## The midpoint value -/

/-- The reflection symmetry pins the value at the midpoint. -/
theorem fabius_half (F : BoundedFabius) (hF : IsFabius F) :
    fabiusReal F (1 / 2) = 1 / 2 := by
  have hs := hF.symmetry (1 / 2) (by constructor <;> norm_num)
  norm_num at hs ⊢
  linarith

/-- The defining equation and the midpoint value give `F'(1/4) = 1`. -/
theorem fabius_deriv_quarter (F : BoundedFabius) (hF : IsFabius F) :
    deriv (fabiusReal F) (1 / 4) = 1 := by
  rw [(hF.hasDerivAt (1 / 4) (by constructor <;> norm_num)).deriv,
    show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num, fabius_half F hF]
  norm_num

/-! ## Monotonicity -/

/-- The differential equation makes the Fabius function monotone on its first half. -/
theorem fabius_monotoneOn_firstHalf (F : BoundedFabius) (hF : IsFabius F) :
    MonotoneOn (fabiusReal F) (Icc (0 : ℝ) (1 / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) (1 / 2))
      hF.contDiff.continuous.continuousOn
      (hF.contDiff.differentiable (by simp)).differentiableOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(hF.hasDerivAt x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).deriv]
  exact mul_nonneg (by norm_num) (fabiusReal_nonneg F (2 * x))

/-- Symmetry transfers first-half monotonicity to the second half. -/
theorem fabius_monotoneOn_secondHalf (F : BoundedFabius) (hF : IsFabius F) :
    MonotoneOn (fabiusReal F) (Icc (1 / 2 : ℝ) 1) := by
  intro x hx y hy hxy
  have hreflectx : 1 - x ∈ Icc (0 : ℝ) (1 / 2) := by
    constructor <;> linarith [hx.1, hx.2]
  have hreflecty : 1 - y ∈ Icc (0 : ℝ) (1 / 2) := by
    constructor <;> linarith [hy.1, hy.2]
  have hmono := fabius_monotoneOn_firstHalf F hF hreflecty hreflectx (by linarith)
  rw [hF.symmetry_all x, hF.symmetry_all y] at hmono
  linarith

/-- The bounded/CDF Fabius function is monotone on all of `ℝ`. -/
theorem fabius_monotone (F : BoundedFabius) (hF : IsFabius F) :
    Monotone (fabiusReal F) := by
  intro x y hxy
  by_cases hy0 : y ≤ 0
  · rw [hF.zero_of_nonpos y hy0, hF.zero_of_nonpos x (hxy.trans hy0)]
  by_cases hx0 : x ≤ 0
  · rw [hF.zero_of_nonpos x hx0]
    exact fabiusReal_nonneg F y
  have hxpos : 0 < x := lt_of_not_ge hx0
  by_cases hx1 : 1 ≤ x
  · rw [hF.one_of_one_le x hx1, hF.one_of_one_le y (hx1.trans hxy)]
  by_cases hy1 : 1 ≤ y
  · rw [hF.one_of_one_le y hy1]
    exact fabiusReal_le_one F x
  have hxmem : x ∈ Icc (0 : ℝ) 1 := ⟨hxpos.le, le_of_not_ge hx1⟩
  have hymem : y ∈ Icc (0 : ℝ) 1 :=
    ⟨le_of_not_ge hy0, le_of_not_ge hy1⟩
  by_cases hyhalf : y ≤ 1 / 2
  · exact fabius_monotoneOn_firstHalf F hF
      ⟨hxmem.1, hxy.trans hyhalf⟩ ⟨hymem.1, hyhalf⟩ hxy
  by_cases hxhalf : 1 / 2 ≤ x
  · exact fabius_monotoneOn_secondHalf F hF
      ⟨hxhalf, hxmem.2⟩ ⟨le_of_not_ge hyhalf, hymem.2⟩ hxy
  · exact (fabius_monotoneOn_firstHalf F hF
        ⟨hxmem.1, le_of_not_ge hxhalf⟩ ⟨by norm_num, by norm_num⟩
          (le_of_not_ge hxhalf)).trans
      (fabius_monotoneOn_secondHalf F hF
        ⟨by norm_num, by norm_num⟩ ⟨le_of_not_ge hyhalf, hymem.2⟩
          (le_of_not_ge hyhalf))

/-! ## Positivity -/

/--
A zero on the first half would force a zero at twice the argument.

This is the bootstrap step used to prove `fabius_pos_of_pos`; once that is
available, `fabius_pos_iff` shows the hypothesis can only hold at `x = 0`.
-/
theorem fabius_zero_double (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2)
    (hz : fabiusReal F x = 0) : fabiusReal F (2 * x) = 0 := by
  have hmin : IsMinOn (fabiusReal F) Set.univ x := by
    intro y hy
    rw [hz]
    exact fabiusReal_nonneg F y
  have hderiv : deriv (fabiusReal F) x = 0 :=
    (hmin.isLocalMin Filter.univ_mem).deriv_eq_zero
  rw [(hF.hasDerivAt x ⟨hx0, hxhalf⟩).deriv] at hderiv
  linarith

/-- The Fabius function is strictly positive at every positive argument. -/
theorem fabius_pos_of_pos (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : 0 < x) : 0 < fabiusReal F x := by
  by_contra hnot
  have hz : fabiusReal F x = 0 :=
    le_antisymm (le_of_not_gt hnot) (fabiusReal_nonneg F x)
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 / 2 : ℝ) / x)
  have hNle : (N : ℝ) ≤ (2 : ℝ) ^ N := by
    exact_mod_cast (Nat.lt_two_pow_self (n := N)).le
  have hex : ∃ n : ℕ, (1 / 2 : ℝ) ≤ (2 : ℝ) ^ n * x := by
    refine ⟨N, ?_⟩
    have : (1 / 2 : ℝ) < (N : ℝ) * x := by
      rw [div_lt_iff₀ hx] at hN
      linarith
    nlinarith
  let n := Nat.find hex
  have hnreach : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ n * x := Nat.find_spec hex
  have hzero_iter : ∀ m : ℕ, m ≤ n →
      fabiusReal F ((2 : ℝ) ^ m * x) = 0 := by
    intro m hm
    induction m with
    | zero => simpa using hz
    | succ m ih =>
        have hm_lt : m < n := by omega
        have hnotreach : ¬ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ m * x := by
          intro hreach
          exact (Nat.not_lt_of_ge (Nat.find_min' hex hreach)) hm_lt
        have hxm_nonneg : 0 ≤ (2 : ℝ) ^ m * x := by positivity
        have hxm_half : (2 : ℝ) ^ m * x ≤ 1 / 2 := le_of_not_ge hnotreach
        have hdoubled := fabius_zero_double F hF hxm_nonneg hxm_half (ih (by omega))
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hdoubled
  have hhalf_le_zero := fabius_monotone F hF
      (show (1 / 2 : ℝ) ≤ (2 : ℝ) ^ n * x from hnreach)
  rw [hzero_iter n le_rfl, fabius_half F hF] at hhalf_le_zero
  norm_num at hhalf_le_zero

/-- Values strictly left of one are strictly below one. -/
theorem fabius_lt_one_of_lt_one (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x < 1) : fabiusReal F x < 1 := by
  have hpos : 0 < fabiusReal F (1 - x) :=
    fabius_pos_of_pos F hF (by linarith)
  rw [hF.symmetry_all x] at hpos
  linarith

/-- Positivity of the bounded Fabius function characterizes the positive half line. -/
theorem fabius_pos_iff (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    0 < fabiusReal F x ↔ 0 < x := by
  refine ⟨fun h => ?_, fun h => fabius_pos_of_pos F hF h⟩
  by_contra hx
  rw [hF.zero_of_nonpos x (le_of_not_gt hx)] at h
  exact lt_irrefl 0 h

/-- Being below one characterizes the arguments strictly left of one. -/
theorem fabius_lt_one_iff (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    fabiusReal F x < 1 ↔ x < 1 := by
  refine ⟨fun h => ?_, fun h => fabius_lt_one_of_lt_one F hF h⟩
  by_contra hx
  rw [hF.one_of_one_le x (le_of_not_gt hx)] at h
  exact lt_irrefl 1 h

/-- The zero set of the bounded Fabius function is the nonpositive half line. -/
theorem fabiusReal_eq_zero_iff (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    fabiusReal F x = 0 ↔ x ≤ 0 := by
  constructor
  · intro h
    by_contra hx
    have hpos := fabius_pos_of_pos F hF (lt_of_not_ge hx)
    rw [h] at hpos
    exact lt_irrefl 0 hpos
  · exact hF.zero_of_nonpos x

/-- The one set of the bounded Fabius function is the half line starting at
one. -/
theorem fabiusReal_eq_one_iff (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    fabiusReal F x = 1 ↔ 1 ≤ x := by
  constructor
  · intro h
    by_contra hx
    have hlt := fabius_lt_one_of_lt_one F hF (lt_of_not_ge hx)
    rw [h] at hlt
    exact lt_irrefl 1 hlt
  · exact hF.one_of_one_le x

/-- The ordinary support of the bounded Fabius function is `(0, ∞)`. -/
theorem support_fabiusReal (F : BoundedFabius) (hF : IsFabius F) :
    Function.support (fabiusReal F) = Ioi (0 : ℝ) := by
  ext x
  change fabiusReal F x ≠ 0 ↔ 0 < x
  exact (not_congr (fabiusReal_eq_zero_iff F hF x)).trans not_le

/-- The topological support of the bounded Fabius function is `[0, ∞)`. -/
theorem tsupport_fabiusReal (F : BoundedFabius) (hF : IsFabius F) :
    tsupport (fabiusReal F) = Ici (0 : ℝ) := by
  have hts : tsupport (fabiusReal F) =
      closure (Function.support (fabiusReal F)) := rfl
  rw [hts, support_fabiusReal F hF, closure_Ioi]

/-! ## The exact support of Rvachev's function -/

/-- Rvachev's function is strictly positive on the interior of its support. -/
theorem rvachevUp_pos_of_mem_Ioo (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : 0 < rvachevUp F x := by
  by_cases hx0 : x ≤ 0
  · rw [rvachevUp_of_nonpos F hx0]
    exact fabius_pos_of_pos F hF (by linarith [hx.1])
  · rw [rvachevUp_of_pos F (lt_of_not_ge hx0)]
    exact fabius_pos_of_pos F hF (by linarith [hx.2])

/-- The support of Rvachev's function is exactly the open interval `(-1,1)`. -/
theorem support_rvachevUp (F : BoundedFabius) (hF : IsFabius F) :
    Function.support (rvachevUp F) = Ioo (-1 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hmem
    exact (Function.mem_support.mp hx)
      (rvachevUp_eq_zero_of_not_mem_Ioo F hF hmem)
  · intro x hx
    exact Function.mem_support.mpr (rvachevUp_pos_of_mem_Ioo F hF hx).ne'

/-- Rvachev's function is supported in `[-1,1]`. -/
theorem support_rvachev_subset (F : BoundedFabius) (hF : IsFabius F) :
    Function.support (rvachevUp F) ⊆ Icc (-1 : ℝ) 1 := by
  rw [support_rvachevUp F hF]
  exact Ioo_subset_Icc_self

/-- The topological support is exactly the compact interval `[-1,1]`. -/
theorem tsupport_rvachev (F : BoundedFabius) (hF : IsFabius F) :
    tsupport (rvachevUp F) = Icc (-1 : ℝ) 1 := by
  have hts : tsupport (rvachevUp F) =
      closure (Function.support (rvachevUp F)) := rfl
  rw [hts, support_rvachevUp F hF,
    closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]

/-! ## Strict monotonicity -/

/-- The derivative of the bounded Fabius function is strictly positive on the
open unit interval. -/
theorem deriv_fabiusReal_pos (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < deriv (fabiusReal F) x := by
  rw [(fabius_hasDerivAt F hF x).deriv]
  have hmem : 2 * x - 1 ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h := rvachevUp_pos_of_mem_Ioo F hF hmem
  linarith

/-- The bounded Fabius function is strictly increasing on the unit interval. -/
theorem strictMonoOn_fabiusReal (F : BoundedFabius) (hF : IsFabius F) :
    StrictMonoOn (fabiusReal F) (Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1)
    hF.contDiff.continuous.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  exact deriv_fabiusReal_pos F hF hx

/-- Strict monotonicity in `iff` form. -/
theorem fabiusReal_lt_fabiusReal_iff (F : BoundedFabius) (hF : IsFabius F)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    fabiusReal F x < fabiusReal F y ↔ x < y :=
  (strictMonoOn_fabiusReal F hF).lt_iff_lt hx hy

/-- The bounded Fabius function is injective on the unit interval. -/
theorem injOn_fabiusReal (F : BoundedFabius) (hF : IsFabius F) :
    Set.InjOn (fabiusReal F) (Icc (0 : ℝ) 1) :=
  (strictMonoOn_fabiusReal F hF).injOn

/-- The bounded Fabius function maps the unit interval onto itself. -/
theorem surjOn_fabiusReal (F : BoundedFabius) (hF : IsFabius F) :
    Set.SurjOn (fabiusReal F) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
  have h := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    (hF.contDiff.continuous.continuousOn (s := Icc (0 : ℝ) 1))
  rwa [hF.zero_of_nonpos 0 le_rfl, hF.one_of_one_le 1 le_rfl] at h

/-- The bounded Fabius function restricts to a bijection of the unit interval
onto itself. -/
theorem bijOn_fabiusReal (F : BoundedFabius) (hF : IsFabius F) :
    Set.BijOn (fabiusReal F) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) :=
  ⟨fun x _ => ⟨fabiusReal_nonneg F x, fabiusReal_le_one F x⟩,
    injOn_fabiusReal F hF, surjOn_fabiusReal F hF⟩

/-! ## Unimodality of Rvachev's function -/

/-- On the nonnegative half line `up` is the reflection of `F`, including at
the fold point. -/
theorem rvachevUp_eq_fabiusReal_one_sub (F : BoundedFabius) {x : ℝ}
    (hx : 0 ≤ x) : rvachevUp F x = fabiusReal F (1 - x) := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, rvachevUp_of_nonpos F le_rfl]
    norm_num
  · exact rvachevUp_of_pos F h

/-- Rvachev's function is strictly decreasing on `[0,1]`. -/
theorem strictAntiOn_rvachevUp (F : BoundedFabius) (hF : IsFabius F) :
    StrictAntiOn (rvachevUp F) (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  rw [rvachevUp_eq_fabiusReal_one_sub F hx.1,
    rvachevUp_eq_fabiusReal_one_sub F hy.1]
  exact strictMonoOn_fabiusReal F hF
    ⟨by linarith [hy.2], by linarith [hy.1]⟩
    ⟨by linarith [hx.2], by linarith [hx.1]⟩ (by linarith)

/-- Rvachev's function is strictly increasing on `[-1,0]`. -/
theorem strictMonoOn_rvachevUp (F : BoundedFabius) (hF : IsFabius F) :
    StrictMonoOn (rvachevUp F) (Icc (-1 : ℝ) 0) := by
  intro x hx y hy hxy
  rw [← rvachevUp_even F x, ← rvachevUp_even F y]
  exact strictAntiOn_rvachevUp F hF
    ⟨by linarith [hy.2], by linarith [hy.1]⟩
    ⟨by linarith [hx.2], by linarith [hx.1]⟩ (by linarith)

/-- Rvachev's function is strictly below one away from the origin. -/
theorem rvachevUp_lt_one_of_ne_zero (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x ≠ 0) : rvachevUp F x < 1 := by
  have key : ∀ y : ℝ, 0 < y → rvachevUp F y < 1 := by
    intro y hy
    rw [rvachevUp_of_pos F hy]
    exact fabius_lt_one_of_lt_one F hF (by linarith)
  rcases lt_or_gt_of_ne hx with h | h
  · rw [← rvachevUp_even F x]
    exact key (-x) (by linarith)
  · exact key x h

/-- The origin is the global maximum of Rvachev's function. -/
theorem isMaxOn_rvachevUp_zero (F : BoundedFabius) (hF : IsFabius F) :
    IsMaxOn (rvachevUp F) Set.univ 0 := by
  intro y _hy
  rw [rvachevUp_zero F hF]
  exact rvachevUp_le_one F y

/-- The maximum of Rvachev's function is attained only at the origin. -/
theorem rvachevUp_eq_one_iff (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    rvachevUp F x = 1 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, rvachevUp_zero F hF]⟩
  by_contra hx
  exact absurd h (ne_of_lt (rvachevUp_lt_one_of_ne_zero F hF hx))

end Fabius
