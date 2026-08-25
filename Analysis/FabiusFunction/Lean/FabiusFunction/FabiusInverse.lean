import FabiusFunction.SharpFlatness
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The inverse of the Fabius function on the unit interval

`FabiusFunction.Monotonicity` proves that a bounded Fabius function restricts
to a bijection of `[0,1]` onto itself, strictly increasing and continuous.
This module constructs the inverse of that bijection and transports the
flatness estimates of `FabiusFunction.EffectiveFlatness` and
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

Two consequences are recorded.  The inverse is steeper than every root at the
origin, and in particular has an infinite one-sided derivative there:
`fabiusInv F hF y / y → ∞` as `y → 0⁺`.  That is the exact mirror of
`F' 0 = 0`.  An effective form is also given: for every slope `M` the inverse
already exceeds `M * y` once `8 * M ^ 2 * y < 1`, where `8 = 2 ^ C(3,2)` is
the flatness constant at `n = 2`.

The right endpoint behaves the same way, by the reflection symmetry
`F (1 - x) = 1 - F x`.  That direction is not developed here.

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
* `le_two_pow_mul_fabiusInv_pow` and
  `le_two_pow_div_factorial_mul_fabiusInv_pow` — the transported flatness
  bounds, with `le_two_pow_mul_fabiusInv_pow_of_le` restating the scale
  hypothesis on the argument.
* `mul_lt_fabiusInv` and `tendsto_fabiusInv_div_atTop` — the effective and
  limiting forms of infinite steepness at the origin.
-/

set_option autoImplicit false

open Filter Set Topology

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

/-- The reflection symmetry fixes the midpoint, hence so does the inverse.

The midpoint is the unique fixed point of `F` in the interior, but it is far
from the only interior value known in closed form: every dyadic rational of
`[0,1]` has an exact rational value, computed by `Arithmetic.fabiusDyadic` and
transferred to `fabiusReal` by `DyadicAnalytic.fabiusDyadicUnit_cast`.  So
`fabiusInv F hF` is likewise known exactly at every such value — for example
`fabiusInv F hF (5/72) = 1/4`, since `F (1/4) = 5/72`. -/
theorem fabiusInv_half (F : BoundedFabius) (hF : IsFabius F) :
    fabiusInv F hF (1 / 2) = 1 / 2 := by
  have h := fabiusInv_fabiusReal F hF
    (show (1 : ℝ) / 2 ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  rwa [fabius_half F hF] at h

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

end Fabius
