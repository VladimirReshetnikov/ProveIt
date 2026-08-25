import FabiusFunction.SharpFlatness
import FabiusFunction.FabiusFlatness
import FabiusFunction.DyadicAnalytic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The inverse of the Fabius function on the unit interval

`FabiusFunction.Monotonicity` proves that a bounded Fabius function restricts
to a bijection of `[0,1]` onto itself, strictly increasing and continuous.
This module constructs the inverse of that bijection and transports both the
qualitative flatness of `FabiusFunction.FabiusFlatness` and the quantitative
estimates of `FabiusFunction.EffectiveFlatness` and
`FabiusFunction.SharpFlatness` through it.

The construction follows Mathlib's own `Real.arcsin`, which solves the same
problem for `sin` on `[-π/2, π/2]`: a strictly monotone continuous bijection
of a closed interval is packaged as an `OrderIso` between the two interval
subtypes, the inverse `OrderIso` is continuous because every `OrderIso`
between order topologies is, and the result is totalized to all of `ℝ` by
`Set.IccExtend`, which clamps its argument into `[0,1]` first.  So

`fabiusInv F hF y = 0` for `y ≤ 0`  and  `fabiusInv F hF y = 1` for `1 ≤ y`,

matching the convention that `F` itself is `0` to the left and `1` to the
right of the unit interval.  With that convention `fabiusInv F hF` is
monotone and continuous on all of `ℝ`, not merely on `[0,1]`.

## Interior calculus

On the open unit interval the derivative of `F` is strictly positive.  The
local inverse theorem therefore applies without any analyticity assumption:

`(fabiusInv F hF)'(y) = 1 / F'(fabiusInv F hF y)
                       = 1 / (2 * up(2 * fabiusInv F hF y - 1)) > 0`.

The formal statements below expose both the `HasDerivAt` result and its
pointwise derivative, explicit `rvachevUp`, positivity, and full `C^∞`
smoothness on `(0,1)`.  The endpoint behavior remains singular, as quantified
by the flatness results.

## Flatness inverts to steepness

The interesting content is what flatness becomes on the other side.  The
Fabius function vanishes at the origin to infinite order: for every `n`,

`F x ≤ 2 ^ C(n+1,2) * x ^ n`   whenever `0 ≤ x` and `2 ^ n * x ≤ 1`,

and with the sharper factorial constant `2 ^ C(n+1,2) / n!`.  Substituting
`x = fabiusInv F hF y` and using `F (fabiusInv F hF y) = y` turns each of
these *upper* bounds on `F` into a *lower* bound on the inverse.  The
inequality reverses, because inverting an increasing function exchanges the
two sides:

`y ≤ 2 ^ C(n+1,2) * (fabiusInv F hF y) ^ n`,   valid for `y ≤ F (2⁻ⁿ)`.

Solving for the inverse would read `fabiusInv F hF y ≥ c_n * y ^ (1/n)`; the
statements below are given in the equivalent root-free form, which avoids
`Real.rpow` and keeps every constant an exact power of two.  Note that the
window of validity shrinks super-exponentially in `n`, so the family cannot
be combined into one bound uniform in `n`.

Two consequences are recorded.  The all-degree little-o statement
`y = o((fabiusInv F hF y)^n)` says exactly, without choosing an `n`-th-root
convention, that the inverse is steeper than every root at the origin.  In
particular it has an infinite one-sided derivative there:
`fabiusInv F hF y / y → ∞` as `y → 0⁺`.  That is the exact mirror of
`F' 0 = 0`.  An effective form is also given: for every slope `M` the inverse
already exceeds `M * y` once `8 * M ^ 2 * y < 1`, where `8 = 2 ^ C(3,2)` is
the flatness constant at `n = 2`.

The right endpoint behaves the same way.  The inverse inherits the exact
reflection symmetry `fabiusInv F hF (1 - y) = 1 - fabiusInv F hF y`, which
transports both the effective slope bound and the divergent difference
quotient from zero to one.

## Main results

* `fabiusOrderIso` — the order isomorphism of `[0,1]` onto itself.
* `fabiusInv` — the totalized inverse, with `fabiusReal_fabiusInv` and
  `fabiusInv_fabiusReal` its two inversion identities on `[0,1]`.
* `continuous_fabiusInv`, `monotone_fabiusInv`, `strictMonoOn_fabiusInv`,
  `bijOn_fabiusInv` — regularity and the inverse bijection.
* `fabiusInv_zero`, `fabiusInv_one`, `fabiusInv_half` — the values at the two
  endpoints and at the fixed point of the reflection.  These are not the only
  closed-form values: `DyadicAnalytic.fabiusDyadicUnit_cast` evaluates `F` at
  every dyadic rational of `[0,1]` exactly, so every such value inverts.  For
  instance `F (1/4) = 5/72`, which is the threshold appearing in
  `mul_lt_fabiusInv` below.
* `fabiusInv_eq_zero_of_nonpos`, `fabiusInv_eq_one_of_one_le`, and
  `fabiusInv_one_sub` — the two constant tails and the global reflection law.
* `fabiusInv_hasDerivAt`, `deriv_fabiusInv`,
  `deriv_fabiusInv_eq_inv_two_mul_rvachevUp`, and `deriv_fabiusInv_pos` — the
  exact positive reciprocal-derivative formula throughout `(0,1)`.
* `fabiusInv_contDiffOn_Ioo` — the inverse is `C^∞` on the whole open unit
  interval.  The global refinements `fabiusInv_contDiffAt_iff` and
  `fabiusInv_differentiableAt_iff` show that the two clamping endpoints are
  exactly the exceptions to positive finite-order or `C^∞` smoothness and
  differentiability; order-zero smoothness, namely continuity, still holds
  globally.
* `fabiusInv_fabiusDyadicUnit` — every value produced by the exact bounded
  dyadic evaluator inverts to the corresponding clamped dyadic argument.
* `le_two_pow_mul_fabiusInv_pow` and
  `le_two_pow_div_factorial_mul_fabiusInv_pow` — the transported flatness
  bounds, with `le_two_pow_mul_fabiusInv_pow_of_le` restating the scale
  hypothesis on the argument.
* `id_isLittleO_fabiusInv_pow_at_zero_right` and
  `one_sub_isLittleO_one_sub_fabiusInv_pow_at_one_left` — the inverse outruns
  every root asymptotically at both clamping endpoints, in root-free form.
* `mul_lt_fabiusInv`, `tendsto_fabiusInv_div_atTop`, and their reflected
  companions — effective and limiting forms of infinite steepness at both
  endpoints.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped ContDiff

namespace Fabius

/-- The bounded Fabius function, viewed as an order isomorphism of the unit
interval onto itself.  It is strictly monotone there by
`strictMonoOn_fabiusReal`, and its image is the whole interval by
`bijOn_fabiusReal`. -/
noncomputable def fabiusOrderIso (F : BoundedFabius) (hF : IsFabius F) :
    Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1 :=
  ((strictMonoOn_fabiusReal F hF).orderIso _ _).trans <|
    OrderIso.setCongr _ _ (bijOn_fabiusReal F hF).image_eq

/-- The order isomorphism is `fabiusReal` on the nose.

This bridging `simp` lemma is what lets the inversion identities below close by
`simpa`.  Without it the two sides differ by an unfolding of `OrderIso.trans`,
`StrictMonoOn.orderIso`, `Set.BijOn.equiv` and `Equiv.setCongr`, none of which
is reducible, and `simpa ... using` performs its final unification at reducible
transparency.  Mathlib carries the same lemma for the same reason next to its
`Real.sinOrderIso`. -/
@[simp] theorem coe_fabiusOrderIso_apply (F : BoundedFabius) (hF : IsFabius F)
    (x : Icc (0 : ℝ) 1) : (fabiusOrderIso F hF x : ℝ) = fabiusReal F x := rfl

/-- The inverse of the bounded Fabius function on `[0,1]`, extended to all of
`ℝ` by clamping the argument into the unit interval.  It therefore takes the
value `0` on `(-∞, 0]` and `1` on `[1, ∞)`, mirroring the convention for `F`
itself. -/
noncomputable def fabiusInv (F : BoundedFabius) (hF : IsFabius F) : ℝ → ℝ :=
  Subtype.val ∘ IccExtend (zero_le_one : (0 : ℝ) ≤ 1) (fabiusOrderIso F hF).symm

/-- The inverse takes values in the unit interval, for every real argument. -/
theorem fabiusInv_mem_Icc (F : BoundedFabius) (hF : IsFabius F) (y : ℝ) :
    fabiusInv F hF y ∈ Icc (0 : ℝ) 1 :=
  Subtype.coe_prop _

/-- The inverse is nonnegative. -/
theorem fabiusInv_nonneg (F : BoundedFabius) (hF : IsFabius F) (y : ℝ) :
    0 ≤ fabiusInv F hF y :=
  (fabiusInv_mem_Icc F hF y).1

/-- The inverse is bounded by one. -/
theorem fabiusInv_le_one (F : BoundedFabius) (hF : IsFabius F) (y : ℝ) :
    fabiusInv F hF y ≤ 1 :=
  (fabiusInv_mem_Icc F hF y).2

/-- `fabiusInv` is a right inverse of `fabiusReal` on the unit interval. -/
theorem fabiusReal_fabiusInv (F : BoundedFabius) (hF : IsFabius F)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    fabiusReal F (fabiusInv F hF y) = y := by
  simpa [fabiusInv, IccExtend_of_mem _ _ hy, -OrderIso.apply_symm_apply] using
    Subtype.ext_iff.1 ((fabiusOrderIso F hF).apply_symm_apply ⟨y, hy⟩)

/-- `fabiusInv` is a left inverse of `fabiusReal` on the unit interval. -/
theorem fabiusInv_fabiusReal (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    fabiusInv F hF (fabiusReal F x) = x :=
  injOn_fabiusReal F hF (fabiusInv_mem_Icc F hF _) hx <| by
    rw [fabiusReal_fabiusInv F hF ⟨fabiusReal_nonneg F x, fabiusReal_le_one F x⟩]

/-- The inverse is strictly increasing on the unit interval. -/
theorem strictMonoOn_fabiusInv (F : BoundedFabius) (hF : IsFabius F) :
    StrictMonoOn (fabiusInv F hF) (Icc (0 : ℝ) 1) :=
  (Subtype.strictMono_coe _).comp_strictMonoOn <|
    (fabiusOrderIso F hF).symm.strictMono.strictMonoOn_IccExtend _

/-- Because the extension clamps its argument, the inverse is monotone on all
of `ℝ`, not merely on the unit interval. -/
theorem monotone_fabiusInv (F : BoundedFabius) (hF : IsFabius F) :
    Monotone (fabiusInv F hF) :=
  (Subtype.mono_coe _).comp <| (fabiusOrderIso F hF).symm.monotone.IccExtend _

/-- The inverse is injective on the unit interval. -/
theorem injOn_fabiusInv (F : BoundedFabius) (hF : IsFabius F) :
    InjOn (fabiusInv F hF) (Icc (0 : ℝ) 1) :=
  (strictMonoOn_fabiusInv F hF).injOn

/-- The inverse is continuous on all of `ℝ`.  Continuity is automatic from the
order isomorphism: every `OrderIso` between spaces carrying the order topology
is a homeomorphism, and `IccExtend` of a continuous map is continuous. -/
theorem continuous_fabiusInv (F : BoundedFabius) (hF : IsFabius F) :
    Continuous (fabiusInv F hF) :=
  continuous_subtype_val.comp (fabiusOrderIso F hF).symm.continuous.Icc_extend'

/-- The inverse restricts to a bijection of the unit interval onto itself. -/
theorem bijOn_fabiusInv (F : BoundedFabius) (hF : IsFabius F) :
    Set.BijOn (fabiusInv F hF) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) :=
  ⟨fun y _ => fabiusInv_mem_Icc F hF y, injOn_fabiusInv F hF,
    fun x hx => ⟨fabiusReal F x,
      ⟨fabiusReal_nonneg F x, fabiusReal_le_one F x⟩,
      fabiusInv_fabiusReal F hF hx⟩⟩

/-- Comparing the inverse against a point of the unit interval is the same as
comparing the argument against the corresponding value of `F`. -/
theorem fabiusInv_le_iff_le_fabiusReal (F : BoundedFabius) (hF : IsFabius F)
    {y x : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    fabiusInv F hF y ≤ x ↔ y ≤ fabiusReal F x := by
  have h := (strictMonoOn_fabiusReal F hF).le_iff_le
    (fabiusInv_mem_Icc F hF y) hx
  rw [fabiusReal_fabiusInv F hF hy] at h
  exact h.symm

/-- The companion comparison equivalence with `fabiusReal` on the left. -/
theorem fabiusReal_le_iff_le_fabiusInv (F : BoundedFabius) (hF : IsFabius F)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    fabiusReal F x ≤ y ↔ x ≤ fabiusInv F hF y := by
  have h := (strictMonoOn_fabiusReal F hF).le_iff_le
    hx (fabiusInv_mem_Icc F hF y)
  rwa [fabiusReal_fabiusInv F hF hy] at h

/-- Strict comparison of the inverse with a point of the unit interval. -/
theorem fabiusInv_lt_iff_lt_fabiusReal (F : BoundedFabius) (hF : IsFabius F)
    {y x : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    fabiusInv F hF y < x ↔ y < fabiusReal F x := by
  have h := (strictMonoOn_fabiusReal F hF).lt_iff_lt
    (fabiusInv_mem_Icc F hF y) hx
  rw [fabiusReal_fabiusInv F hF hy] at h
  exact h.symm

/-- Strict comparison of a point of the unit interval with the inverse. -/
theorem fabiusReal_lt_iff_lt_fabiusInv (F : BoundedFabius) (hF : IsFabius F)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    fabiusReal F x < y ↔ x < fabiusInv F hF y := by
  have h := (strictMonoOn_fabiusReal F hF).lt_iff_lt
    hx (fabiusInv_mem_Icc F hF y)
  rwa [fabiusReal_fabiusInv F hF hy] at h

/-! ## Interior calculus -/

/-- The inverse maps the open unit interval into itself. -/
theorem fabiusInv_mem_Ioo (F : BoundedFabius) (hF : IsFabius F)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : fabiusInv F hF y ∈ Ioo (0 : ℝ) 1 := by
  have hy' : y ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hy
  constructor
  · apply (fabiusReal_lt_iff_lt_fabiusInv F hF
      (left_mem_Icc.2 zero_le_one) hy').mp
    simpa [fabiusReal, hF.zero_of_nonpos 0 le_rfl] using hy.1
  · apply (fabiusInv_lt_iff_lt_fabiusReal F hF hy'
      (right_mem_Icc.2 zero_le_one)).mpr
    simpa [fabiusReal, hF.one_of_one_le 1 le_rfl] using hy.2

/-- The inverse is differentiable at every interior point, with derivative the
reciprocal of the derivative of `fabiusReal` at the inverse point. -/
theorem fabiusInv_hasDerivAt (F : BoundedFabius) (hF : IsFabius F)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fabiusInv F hF)
      (deriv (fabiusReal F) (fabiusInv F hF y))⁻¹ y := by
  have hx := fabiusInv_mem_Ioo F hF hy
  have hderiv : deriv (fabiusReal F) (fabiusInv F hF y) ≠ 0 :=
    (deriv_fabiusReal_pos F hF hx).ne'
  refine ((fabius_differentiable F hF _).hasDerivAt).of_local_left_inverse
    (continuous_fabiusInv F hF).continuousAt hderiv ?_
  filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
  exact fabiusReal_fabiusInv F hF (Ioo_subset_Icc_self ht)

/-- Compatibility spelling for the interior inverse-derivative theorem. -/
theorem hasDerivAt_fabiusInv (F : BoundedFabius) (hF : IsFabius F)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fabiusInv F hF)
      (deriv (fabiusReal F) (fabiusInv F hF y))⁻¹ y :=
  fabiusInv_hasDerivAt F hF hy

/-- Pointwise reciprocal-derivative formula for the inverse on `(0,1)`. -/
theorem deriv_fabiusInv (F : BoundedFabius) (hF : IsFabius F)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    deriv (fabiusInv F hF) y =
      (deriv (fabiusReal F) (fabiusInv F hF y))⁻¹ :=
  (fabiusInv_hasDerivAt F hF hy).deriv

/-- Explicit inverse-derivative formula through Rvachev's up-function. -/
theorem deriv_fabiusInv_eq_inv_two_mul_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    deriv (fabiusInv F hF) y =
      (2 * rvachevUp F (2 * fabiusInv F hF y - 1))⁻¹ := by
  rw [deriv_fabiusInv F hF hy,
    congrFun (deriv_fabiusReal F hF) (fabiusInv F hF y)]

/-- The inverse has strictly positive derivative throughout `(0,1)`. -/
theorem deriv_fabiusInv_pos (F : BoundedFabius) (hF : IsFabius F)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    0 < deriv (fabiusInv F hF) y := by
  rw [deriv_fabiusInv F hF hy]
  exact inv_pos.mpr (deriv_fabiusReal_pos F hF (fabiusInv_mem_Ioo F hF hy))

/-- The totalized inverse of a bounded Fabius function is smooth on the open
unit interval. -/
theorem fabiusInv_contDiffOn_Ioo (F : BoundedFabius) (hF : IsFabius F) :
    ContDiffOn ℝ ∞ (fabiusInv F hF) (Ioo (0 : ℝ) 1) := by
  rw [contDiffOn_infty]
  intro n
  induction n with
  | zero =>
      exact contDiffOn_zero.mpr (continuous_fabiusInv F hF).continuousOn
  | succ n ih =>
      rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
      refine ⟨?_, by simp, ?_⟩
      · intro y hy
        exact (fabiusInv_hasDerivAt F hF hy).differentiableAt.differentiableWithinAt
      · have hderivF : ContDiff ℝ ∞ (deriv (fabiusReal F)) :=
          (contDiff_infty_iff_deriv.mp hF.contDiff).2
        have hderivF_n : ContDiff ℝ n (deriv (fabiusReal F)) :=
          (contDiff_infty.mp hderivF) n
        have hcomp : ContDiffOn ℝ n
            (fun y => deriv (fabiusReal F) (fabiusInv F hF y))
            (Ioo (0 : ℝ) 1) := by
          simpa only [Function.comp_def] using
            hderivF_n.contDiffOn.comp ih (mapsTo_univ _ _)
        apply (hcomp.inv fun y hy =>
          (deriv_fabiusReal_pos F hF
            (fabiusInv_mem_Ioo F hF hy)).ne').congr
        intro y hy
        exact deriv_fabiusInv F hF hy

/-! ## Exact values -/

/-- `F` fixes the origin, hence so does its inverse. -/
@[simp] theorem fabiusInv_zero (F : BoundedFabius) (hF : IsFabius F) :
    fabiusInv F hF 0 = 0 := by
  have h := fabiusInv_fabiusReal F hF
    (left_mem_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1))
  rwa [hF.zero_of_nonpos 0 le_rfl] at h

/-- `F` fixes the right endpoint, hence so does its inverse. -/
@[simp] theorem fabiusInv_one (F : BoundedFabius) (hF : IsFabius F) :
    fabiusInv F hF 1 = 1 := by
  have h := fabiusInv_fabiusReal F hF
    (right_mem_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1))
  rwa [hF.one_of_one_le 1 le_rfl] at h

/-- The totalized inverse is zero on the whole nonpositive half line. -/
theorem fabiusInv_eq_zero_of_nonpos (F : BoundedFabius) (hF : IsFabius F)
    {y : ℝ} (hy : y ≤ 0) : fabiusInv F hF y = 0 := by
  have hmono := monotone_fabiusInv F hF hy
  rw [fabiusInv_zero F hF] at hmono
  exact le_antisymm hmono (fabiusInv_nonneg F hF y)

/-- The totalized inverse is one on the whole half line starting at one. -/
theorem fabiusInv_eq_one_of_one_le (F : BoundedFabius) (hF : IsFabius F)
    {y : ℝ} (hy : 1 ≤ y) : fabiusInv F hF y = 1 := by
  have hmono := monotone_fabiusInv F hF hy
  rw [fabiusInv_one F hF] at hmono
  exact le_antisymm (fabiusInv_le_one F hF y) hmono

/-- Away from the two clamping endpoints, the totalized inverse is smooth.
This combines interior smoothness with the locally constant tails; no sign or
interval-membership case has to be supplied by callers. -/
theorem fabiusInv_contDiffAt (F : BoundedFabius) (hF : IsFabius F)
    {y : ℝ} (hy0 : y ≠ 0) (hy1 : y ≠ 1) :
    ContDiffAt ℝ ∞ (fabiusInv F hF) y := by
  rcases hy0.lt_or_gt with hy0 | hy0
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hy0] with t ht
    exact fabiusInv_eq_zero_of_nonpos F hF ht.le
  · rcases hy1.lt_or_gt with hy1 | hy1
    · exact (fabiusInv_contDiffOn_Ioo F hF).contDiffAt
        (isOpen_Ioo.mem_nhds ⟨hy0, hy1⟩)
    · refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hy1] with t ht
      exact fabiusInv_eq_one_of_one_le F hF ht.le

/-- The inverse inherits the Fabius reflection symmetry on the whole real
line, including both clamped tails. -/
theorem fabiusInv_one_sub (F : BoundedFabius) (hF : IsFabius F) (y : ℝ) :
    fabiusInv F hF (1 - y) = 1 - fabiusInv F hF y := by
  by_cases hy0 : y ≤ 0
  · rw [fabiusInv_eq_zero_of_nonpos F hF hy0,
      fabiusInv_eq_one_of_one_le F hF (by linarith)]
    norm_num
  · by_cases hy1 : 1 ≤ y
    · rw [fabiusInv_eq_one_of_one_le F hF hy1,
        fabiusInv_eq_zero_of_nonpos F hF (by linarith)]
      norm_num
    · have hy : y ∈ Icc (0 : ℝ) 1 :=
        ⟨le_of_not_ge hy0, le_of_not_ge hy1⟩
      have hone : 1 - y ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [hy.1, hy.2]
      have hinv := fabiusInv_mem_Icc F hF y
      have hreflected : 1 - fabiusInv F hF y ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [hinv.1, hinv.2]
      apply injOn_fabiusReal F hF (fabiusInv_mem_Icc F hF (1 - y)) hreflected
      rw [fabiusReal_fabiusInv F hF hone,
        hF.symmetry_all (fabiusInv F hF y),
        fabiusReal_fabiusInv F hF hy]

/-- The reflection symmetry fixes the midpoint, hence so does the inverse.

The midpoint is the unique fixed point of `F` in the interior, but it is far
from the only interior value known in closed form: every dyadic rational of
`[0,1]` has an exact rational value, computed by `Arithmetic.fabiusDyadic` and
transferred to `fabiusReal` by `DyadicAnalytic.fabiusDyadicUnit_cast`.  So
`fabiusInv F hF` is likewise known exactly at every such value — for example
`fabiusInv F hF (5/72) = 1/4`, since `F (1/4) = 5/72`. -/
theorem fabiusInv_half (F : BoundedFabius) (hF : IsFabius F) :
    fabiusInv F hF (1 / 2) = 1 / 2 := by
  have h := fabiusInv_one_sub F hF ((1 : ℝ) / 2)
  norm_num at h ⊢
  linarith

/-- On a dyadic point of the unit grid, the exact bounded evaluator inverts
back to that point. -/
theorem fabiusInv_fabiusDyadicUnit_of_le (F : BoundedFabius) (hF : IsFabius F)
    (n a : ℕ) (ha : a ≤ 2 ^ n) :
    fabiusInv F hF (fabiusDyadicUnit n a : ℝ) =
      (a : ℝ) / (2 : ℝ) ^ n := by
  rw [fabiusDyadicUnit_cast F hF]
  apply fabiusInv_fabiusReal F hF
  constructor
  · positivity
  · rw [div_le_one (by positivity)]
    exact_mod_cast ha

/-- Every value of the exact bounded dyadic evaluator inverts to its clamped
dyadic argument.  Numerators at or beyond the unit grid therefore invert to
one. -/
theorem fabiusInv_fabiusDyadicUnit (F : BoundedFabius) (hF : IsFabius F)
    (n a : ℕ) :
    fabiusInv F hF (fabiusDyadicUnit n a : ℝ) =
      (min a (2 ^ n) : ℕ) / (2 : ℝ) ^ n := by
  by_cases ha : a ≤ 2 ^ n
  · rw [Nat.min_eq_left ha]
    exact fabiusInv_fabiusDyadicUnit_of_le F hF n a ha
  · have hge : 2 ^ n ≤ a := le_of_not_ge ha
    rw [Nat.min_eq_right hge, fabiusDyadicUnit_of_ge n a hge]
    norm_num [fabiusInv_one F hF]

/-! ## Flatness at the origin, transported through the inverse -/

/-- **Effective flatness, inverted.**  The bound `F x ≤ 2 ^ C(n+1,2) * x ^ n`
becomes a lower bound on the inverse.  The scale hypothesis is stated on the
inverse itself; `le_two_pow_mul_fabiusInv_pow_of_le` restates it in terms of
the argument. -/
theorem le_two_pow_mul_fabiusInv_pow (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1)
    (hscale : (2 : ℝ) ^ n * fabiusInv F hF y ≤ 1) :
    y ≤ 2 ^ (n + 1).choose 2 * fabiusInv F hF y ^ n := by
  have h := fabiusReal_le_two_pow_mul_pow F hF n (fabiusInv_nonneg F hF y) hscale
  rwa [fabiusReal_fabiusInv F hF hy] at h

/-- **Sharp flatness, inverted.**  The same statement with the factorial
constant of `FabiusFunction.SharpFlatness`. -/
theorem le_two_pow_div_factorial_mul_fabiusInv_pow (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1)
    (hscale : (2 : ℝ) ^ n * fabiusInv F hF y ≤ 1) :
    y ≤ 2 ^ (n + 1).choose 2 / (n.factorial : ℝ) * fabiusInv F hF y ^ n := by
  have h := fabiusReal_le_two_pow_div_factorial_mul_pow F hF n
    (fabiusInv_nonneg F hF y) hscale
  rwa [fabiusReal_fabiusInv F hF hy] at h

/-- The dyadic point `2⁻ⁿ` lies in the unit interval. -/
private lemma inv_two_pow_mem_Icc (n : ℕ) : ((2 : ℝ)⁻¹) ^ n ∈ Icc (0 : ℝ) 1 := by
  refine ⟨by positivity, ?_⟩
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  calc ((2 : ℝ)⁻¹) ^ n = 1 / (2 : ℝ) ^ n := by rw [inv_pow, one_div]
    _ ≤ 1 := by rw [div_le_one hpos]; exact hone

/-- The scale hypothesis of `le_two_pow_mul_fabiusInv_pow`, restated on the
argument: it suffices that `y` lies below the value of `F` at `2⁻ⁿ`.  This
window shrinks super-exponentially in `n`, so the family cannot be combined
into a single bound uniform in `n`. -/
theorem le_two_pow_mul_fabiusInv_pow_of_le (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ fabiusReal F (((2 : ℝ)⁻¹) ^ n)) :
    y ≤ 2 ^ (n + 1).choose 2 * fabiusInv F hF y ^ n := by
  have hmem := inv_two_pow_mem_Icc n
  have hy1 : y ∈ Icc (0 : ℝ) 1 := ⟨hy0, hy.trans (fabiusReal_le_one F _)⟩
  have hle : fabiusInv F hF y ≤ ((2 : ℝ)⁻¹) ^ n :=
    (fabiusInv_le_iff_le_fabiusReal F hF hy1 hmem).2 hy
  have hscale : (2 : ℝ) ^ n * fabiusInv F hF y ≤ 1 := by
    calc (2 : ℝ) ^ n * fabiusInv F hF y
        ≤ (2 : ℝ) ^ n * ((2 : ℝ)⁻¹) ^ n :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 1 := by rw [← mul_pow]; norm_num
  exact le_two_pow_mul_fabiusInv_pow F hF n hy1 hscale

/-! ## All-order asymptotic steepness -/

/-- **The inverse outruns every root at the origin.**  For every natural `n`,

`y = o((fabiusInv F hF y) ^ n)` as `y → 0⁺`.

This is the root-free form of saying that `fabiusInv F hF y` decays more
slowly than `y ^ (1 / n)` for every positive `n`.  The statement deliberately
also includes `n = 0`, where it reduces to the ordinary fact `y = o(1)`.

The proof composes the two-sided flatness of `fabiusReal F` with continuity of
the totalized inverse.  Restricting to `y < 1` eventually supplies the exact
inverse identity; no quantitative dyadic cutoff is required. -/
theorem id_isLittleO_fabiusInv_pow_at_zero_right
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (fun y : ℝ => y) =o[𝓝[>] (0 : ℝ)] (fun y : ℝ => fabiusInv F hF y ^ n) := by
  have hinv0 : Tendsto (fabiusInv F hF) (nhds (0 : ℝ)) (nhds (0 : ℝ)) :=
    (continuous_fabiusInv F hF).tendsto' 0 0 (fabiusInv_zero F hF)
  have hinv : Tendsto (fabiusInv F hF) (𝓝[>] (0 : ℝ)) (nhds (0 : ℝ)) :=
    hinv0.mono_left nhdsWithin_le_nhds
  have h := (fabiusReal_isLittleO_pow_at_zero F hF n).comp_tendsto hinv
  refine h.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with y hy0 hy1
  exact fabiusReal_fabiusInv F hF ⟨hy0.le, hy1.le⟩

/-- Reflection carries the left-hand neighborhood of one to the right-hand
neighborhood of zero. -/
private theorem tendsto_one_sub_nhdsLT_one_nhdsGT_zero :
    Tendsto (fun y : ℝ => 1 - y) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcontinuous : Continuous (fun y : ℝ => 1 - y) := by fun_prop
    have hat : Tendsto (fun y : ℝ => 1 - y) (nhds (1 : ℝ))
        (nhds (1 - (1 : ℝ))) :=
      hcontinuous.continuousAt
    have hat' : Tendsto (fun y : ℝ => 1 - y) (nhds (1 : ℝ)) (nhds 0) := by
      simpa only [sub_self] using hat
    exact hat'.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    change 0 < 1 - y
    exact sub_pos.mpr hy

/-- **The inverse outruns every reflected root at the right endpoint.**  For
every natural `n`,

`1 - y = o((1 - fabiusInv F hF y) ^ n)` as `y → 1⁻`.

The endpoint and the zero-degree case are already handled by the little-o
statement, so no positivity assumption on `n` or separate boundary wrapper is
needed. -/
theorem one_sub_isLittleO_one_sub_fabiusInv_pow_at_one_left
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (fun y : ℝ => 1 - y) =o[𝓝[<] (1 : ℝ)]
      (fun y : ℝ => (1 - fabiusInv F hF y) ^ n) := by
  have h := (id_isLittleO_fabiusInv_pow_at_zero_right F hF n).comp_tendsto
    tendsto_one_sub_nhdsLT_one_nhdsGT_zero
  refine h.congr' (Filter.Eventually.of_forall fun _ => rfl) ?_
  filter_upwards with y
  change fabiusInv F hF (1 - y) ^ n = (1 - fabiusInv F hF y) ^ n
  rw [fabiusInv_one_sub F hF y]

/-! ## Infinite steepness at the origin -/

/-- **The inverse outruns every linear function at the origin, effectively.**
For every slope `M`, once `y` is positive, below `F (1/4) = 5/72`, and small
enough that `8 * M ^ 2 * y < 1`, the inverse already exceeds `M * y`.  The
constant `8` is `2 ^ C(3,2)`, the flatness constant at `n = 2`; the threshold
`F (1/4)` is exactly `5 / 72` by the dyadic evaluation of
`DyadicAnalytic.fabiusDyadicUnit_cast`.

No positivity is assumed of `M`: for `M ≤ 0` the conclusion is weaker than the
positive case but the same proof gives it, so requiring `0 < M` would only
restrict the statement.

Consequently `fabiusInv F hF` is not Lipschitz at `0`, and it is not Hölder
continuous of any positive exponent there either: running the same argument at
index `n` gives `fabiusInv F hF y ≥ (y / 2 ^ C(n+1,2)) ^ (1/n)`, which beats
`y ^ α` for every `α > 1/n`. -/
theorem mul_lt_fabiusInv (F : BoundedFabius) (hF : IsFabius F)
    {M y : ℝ} (hy0 : 0 < y)
    (hy : y ≤ fabiusReal F (((2 : ℝ)⁻¹) ^ 2))
    (hsmall : 8 * M ^ 2 * y < 1) :
    M * y < fabiusInv F hF y := by
  by_contra hcon
  have hle : fabiusInv F hF y ≤ M * y := not_lt.mp hcon
  have hflat := le_two_pow_mul_fabiusInv_pow_of_le F hF 2 hy0.le hy
  have hchoose : (2 + 1).choose 2 = 3 := by decide
  rw [hchoose] at hflat
  have height : (2 : ℝ) ^ (3 : ℕ) = 8 := by norm_num
  rw [height] at hflat
  have hpow : fabiusInv F hF y ^ 2 ≤ (M * y) ^ 2 :=
    pow_le_pow_left₀ (fabiusInv_nonneg F hF y) hle 2
  have hbound : y ≤ 8 * (M * y) ^ 2 := by linarith
  nlinarith [hbound, hsmall, hy0]

/-- **The inverse has an infinite right derivative at the origin.**  Its
difference quotient at `0` diverges:

`fabiusInv F hF y / y → ∞`  as  `y → 0⁺`.

This is the exact mirror of the vanishing of `F'` at the origin, and it is why
the inverse admits no finite one-sided derivative there. -/
theorem tendsto_fabiusInv_div_atTop (F : BoundedFabius) (hF : IsFabius F) :
    Tendsto (fun y : ℝ => fabiusInv F hF y / y) (𝓝[>] (0 : ℝ)) atTop := by
  have hquarter : (0 : ℝ) < fabiusReal F (((2 : ℝ)⁻¹) ^ 2) :=
    fabius_pos_of_pos F hF (by norm_num)
  rw [tendsto_atTop]
  intro M
  have hc : (0 : ℝ) < 8 * (|M| + 1) ^ 2 := by positivity
  have hthr : (0 : ℝ) < (8 * (|M| + 1) ^ 2)⁻¹ := by positivity
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hquarter),
    nhdsWithin_le_nhds (Iio_mem_nhds hthr)] with y hy1 hy2 hy3
  have hy0 : (0 : ℝ) < y := hy1
  have hsmall : 8 * (|M| + 1) ^ 2 * y < 1 := by
    have h := mul_lt_mul_of_pos_left
      (show y < (8 * (|M| + 1) ^ 2)⁻¹ from hy3) hc
    rwa [mul_inv_cancel₀ hc.ne'] at h
  have hlt : (|M| + 1) * y < fabiusInv F hF y :=
    mul_lt_fabiusInv F hF hy0 (le_of_lt hy2) hsmall
  have hstep : |M| + 1 ≤ fabiusInv F hF y / y := by
    rw [le_div_iff₀ hy0]
    exact hlt.le
  have hMle : M ≤ |M| + 1 := by
    have := le_abs_self M
    linarith
  exact hMle.trans hstep

/-! ## Infinite steepness at the right endpoint -/

/-- The effective slope bound reflected from zero to one.  Once `y < 1` is
close enough to one, the complementary inverse exceeds every prescribed
multiple of the remaining distance to the endpoint. -/
theorem mul_one_sub_lt_one_sub_fabiusInv (F : BoundedFabius) (hF : IsFabius F)
    {M y : ℝ} (hy1 : y < 1)
    (hy : 1 - y ≤ fabiusReal F (((2 : ℝ)⁻¹) ^ 2))
    (hsmall : 8 * M ^ 2 * (1 - y) < 1) :
    M * (1 - y) < 1 - fabiusInv F hF y := by
  have h := mul_lt_fabiusInv F hF (sub_pos.mpr hy1) hy hsmall
  rwa [fabiusInv_one_sub F hF y] at h

/-- The complementary difference quotient at one diverges from the left:

`(1 - fabiusInv F hF y) / (1 - y) → ∞` as `y → 1⁻`.

This is the reflection of `tendsto_fabiusInv_div_atTop`. -/
theorem tendsto_one_sub_fabiusInv_div_one_sub_atTop
    (F : BoundedFabius) (hF : IsFabius F) :
    Tendsto (fun y : ℝ => (1 - fabiusInv F hF y) / (1 - y))
      (𝓝[<] (1 : ℝ)) atTop := by
  have h := (tendsto_fabiusInv_div_atTop F hF).comp
    tendsto_one_sub_nhdsLT_one_nhdsGT_zero
  have heq :
      ((fun y : ℝ => fabiusInv F hF y / y) ∘ fun y : ℝ => 1 - y) =
        fun y : ℝ => (1 - fabiusInv F hF y) / (1 - y) := by
    funext y
    rw [Function.comp_apply, fabiusInv_one_sub F hF y]
  rwa [heq] at h

/-! ## Exact smoothness locus -/

/-- The totalized inverse is not differentiable at the left clamping point.
The local inverse identity on `[0,1]` would otherwise contradict the vanishing
derivative of `fabiusReal` at zero. -/
theorem fabiusInv_not_differentiableAt_zero
    (F : BoundedFabius) (hF : IsFabius F) :
    ¬ DifferentiableAt ℝ (fabiusInv F hF) 0 := by
  intro hdiff
  have hnot : ¬ DifferentiableWithinAt ℝ (fabiusInv F hF)
      (Icc (0 : ℝ) 1) 0 := by
    apply not_differentiableWithinAt_of_local_left_inverse_hasDerivWithinAt_zero
      (f := fabiusReal F) (g := fabiusInv F hF)
      (s := Icc (0 : ℝ) 1) (t := Icc (0 : ℝ) 1)
      (left_mem_Icc.2 zero_le_one)
      (uniqueDiffOn_Icc_zero_one 0 (left_mem_Icc.2 zero_le_one))
      (by simpa only [fabiusInv_zero] using
        (fabius_hasDerivAt_zero F hF).hasDerivWithinAt)
      (fun y _hy => fabiusInv_mem_Icc F hF y)
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact fabiusReal_fabiusInv F hF hy
  exact hnot hdiff.differentiableWithinAt

/-- The totalized inverse is not differentiable at the right clamping point.
The symmetric local inverse argument uses the vanishing derivative of
`fabiusReal` at one. -/
theorem fabiusInv_not_differentiableAt_one
    (F : BoundedFabius) (hF : IsFabius F) :
    ¬ DifferentiableAt ℝ (fabiusInv F hF) 1 := by
  intro hdiff
  have hnot : ¬ DifferentiableWithinAt ℝ (fabiusInv F hF)
      (Icc (0 : ℝ) 1) 1 := by
    apply not_differentiableWithinAt_of_local_left_inverse_hasDerivWithinAt_zero
      (f := fabiusReal F) (g := fabiusInv F hF)
      (s := Icc (0 : ℝ) 1) (t := Icc (0 : ℝ) 1)
      (right_mem_Icc.2 zero_le_one)
      (uniqueDiffOn_Icc_zero_one 1 (right_mem_Icc.2 zero_le_one))
      (by simpa only [fabiusInv_one] using
        (fabius_hasDerivAt_one F hF).hasDerivWithinAt)
      (fun y _hy => fabiusInv_mem_Icc F hF y)
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact fabiusReal_fabiusInv F hF hy
  exact hnot hdiff.differentiableWithinAt

/-- Exact differentiability locus of the totalized inverse: the inverse is
smooth in the open interval and on both constant tails, but not at either
clamping endpoint. -/
theorem fabiusInv_differentiableAt_iff
    (F : BoundedFabius) (hF : IsFabius F) (y : ℝ) :
    DifferentiableAt ℝ (fabiusInv F hF) y ↔ y ≠ 0 ∧ y ≠ 1 := by
  constructor
  · intro hdiff
    constructor
    · intro hy
      subst y
      exact fabiusInv_not_differentiableAt_zero F hF hdiff
    · intro hy
      subst y
      exact fabiusInv_not_differentiableAt_one F hF hdiff
  · rintro ⟨hy0, hy1⟩
    exact (fabiusInv_contDiffAt F hF hy0 hy1).differentiableAt (by simp)

/-- Exact finite-order or `C∞` smoothness locus of the totalized inverse.

Order zero is continuity, which holds globally.  At every positive order the
two clamping endpoints are the exact exceptions, while all other points are
in a constant tail or in the smooth open interval.  The hypothesis `n ≤ ∞`
is essential: `ℕ∞ω` also has the strictly stronger analytic order `ω`, and the
inverse is not analytic in the interior. -/
theorem fabiusInv_contDiffAt_iff
    (F : BoundedFabius) (hF : IsFabius F) (y : ℝ) {n : ℕ∞ω} (hn : n ≤ ∞) :
    ContDiffAt ℝ n (fabiusInv F hF) y ↔ n = 0 ∨ (y ≠ 0 ∧ y ≠ 1) := by
  constructor
  · intro hsmooth
    by_cases hn0 : n = 0
    · exact Or.inl hn0
    · exact Or.inr <| (fabiusInv_differentiableAt_iff F hF y).mp
        (hsmooth.differentiableAt hn0)
  · rintro (rfl | ⟨hy0, hy1⟩)
    · exact (contDiff_zero.mpr (continuous_fabiusInv F hF)).contDiffAt
    · exact (fabiusInv_contDiffAt F hF hy0 hy1).of_le hn

/-- The `C∞` specialization of `fabiusInv_contDiffAt_iff`, without an order
side condition. -/
theorem fabiusInv_contDiffAt_infty_iff
    (F : BoundedFabius) (hF : IsFabius F) (y : ℝ) :
    ContDiffAt ℝ ∞ (fabiusInv F hF) y ↔ y ≠ 0 ∧ y ≠ 1 := by
  simpa using (fabiusInv_contDiffAt_iff F hF y (n := ∞) le_rfl)

/-- Setwise form of `fabiusInv_contDiffAt_infty_iff`: the inverse is `C∞` on
the complement of the two clamping endpoints. -/
theorem fabiusInv_contDiffOn_compl_endpoints
    (F : BoundedFabius) (hF : IsFabius F) :
    ContDiffOn ℝ ∞ (fabiusInv F hF) ({0, 1} : Set ℝ)ᶜ := by
  intro y hy
  have hne : y ≠ 0 ∧ y ≠ 1 := by
    simpa only [Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] using hy
  exact (fabiusInv_contDiffAt F hF hne.1 hne.2).contDiffWithinAt

end Fabius
