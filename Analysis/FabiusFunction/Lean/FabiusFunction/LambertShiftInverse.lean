import FabiusFunction.LambertWElementaryBounds
import FabiusFunction.MeanValueBracket

/-!
# The inverse of `x ↦ x + W(x)`

The Lambert-inverse transseries drafts study the compositional inverse `g` of
the shifted map `f(x) = x + W(x)` (principal branch, `x ≥ 0`).  Their exact
starting point is the reduction

`g(z) = z - u = u e^u`, where `u = u(z) ≥ 0` is the unique root of `u e^u + u = z`,

together with the bracket `z - W(z) < g(z) < z` for `z > 0`, and the residual
certificate: since `1 ≤ f' ≤ 2` on `[0, ∞)`, any candidate `x̃ ≥ 0` with residual
`R = f(x̃) - z` satisfies `|R|/2 ≤ |x̃ - g(z)| ≤ |R|`.

This module formalizes exactly that layer:

* `lambertShift` is `f`; it is a strictly increasing continuous bijection of
  `[0, ∞)` onto itself (`lambertShift_strictMonoOn`, `lambertShift_surjOn`).
* `shiftedLambertW` is the root `u(z)` (the `r`-Lambert function with `r = 1`),
  with its defining identity `shiftedLambertW_mul_exp_add` and uniqueness.
* `lambertShiftInv` is `g`; the two-sided inverse laws are
  `lambertShift_lambertShiftInv` and `lambertShiftInv_lambertShift`, and
  `lambertShiftInv_eq_mul_exp` is `g(z) = u e^u`.
* `lambertShiftInv_lt_self`, `sub_principalLambertW_lt_lambertShiftInv` are the
  bracket, and `abs_sub_lambertShiftInv_le_abs_residual`,
  `abs_residual_le_two_mul_abs_sub_lambertShiftInv` the residual certificate.
  The two Lipschitz brackets behind that certificate are instances of the
  general `MeanValueBracket` lemmas at `m = 1`, `M = 2`.
* `lambertShiftInv_hasDerivAt` differentiates `g` by the inverse-function rule,
  and `deriv_lambertShiftInv_bounds` is `1/2 < g' < 1` on the open half-line.
* `strictConvexOn_lambertShiftInv`: `g` is strictly convex on the open
  half-line, the counterpart of the concavity of `f`.
-/

set_option autoImplicit false

namespace Fabius

open Set

/-- The shifted Lambert map `f(x) = x + W(x)`. -/
noncomputable def lambertShift (x : ℝ) : ℝ := x + principalLambertW x

/-- `u e^u + u`, whose inverse on `[0,∞)` is the `r = 1` Lambert function. -/
noncomputable def shiftedMulExp (u : ℝ) : ℝ := u * Real.exp u + u

/-- Every nonnegative real lies weakly above the Lambert branch point `-e⁻¹`. -/
theorem neg_exp_neg_one_le_of_nonneg {x : ℝ} (hx : 0 ≤ x) : -Real.exp (-1) ≤ x := by
  have := Real.exp_pos (-1)
  linarith

/-- Every nonnegative real lies strictly above the Lambert branch point `-e⁻¹`. -/
theorem neg_exp_neg_one_lt_of_nonneg {x : ℝ} (hx : 0 ≤ x) : -Real.exp (-1) < x := by
  have := Real.exp_pos (-1)
  linarith

/-- `f` is strictly increasing on `[0,∞)`. -/
theorem lambertShift_strictMonoOn : StrictMonoOn lambertShift (Ici 0) := by
  intro a ha b hb hab
  unfold lambertShift
  have := principalLambertW_strictMonoOn (mem_Ici.mpr (neg_exp_neg_one_le_of_nonneg ha))
    (mem_Ici.mpr (neg_exp_neg_one_le_of_nonneg hb)) hab
  linarith

/-- The shifted Lambert map is continuous on the nonnegative half-line. -/
theorem lambertShift_continuousOn : ContinuousOn lambertShift (Ici 0) :=
  continuousOn_id.add (principalLambertW_continuousOn_Ici.mono
    fun _ hx => mem_Ici.mpr (neg_exp_neg_one_le_of_nonneg hx))

/-- The shifted Lambert map fixes zero. -/
theorem lambertShift_zero : lambertShift 0 = 0 := by
  unfold lambertShift
  have h := principalLambertW_unique (z := 0) (w := 0) (neg_exp_neg_one_le_of_nonneg le_rfl)
    (by norm_num) (by simp)
  rw [← h]
  simp

/-- The shifted Lambert map is nonnegative on the nonnegative half-line. -/
theorem lambertShift_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ lambertShift x := by
  unfold lambertShift
  have := principalLambertW_nonneg hx
  linarith

/-- On the nonnegative half-line, the shifted Lambert map is at most `2x`. -/
theorem lambertShift_le_two_mul {x : ℝ} (hx : 0 ≤ x) : lambertShift x ≤ 2 * x := by
  unfold lambertShift
  have := principalLambertW_le_self hx
  linarith

/-- `u e^u + u` is strictly increasing on `[0,∞)`. -/
theorem shiftedMulExp_strictMonoOn : StrictMonoOn shiftedMulExp (Ici 0) := by
  intro a ha b hb hab
  unfold shiftedMulExp
  have := mul_exp_strictMonoOn (mem_Ici.mpr (by linarith [mem_Ici.mp ha]))
    (mem_Ici.mpr (by linarith [mem_Ici.mp hb])) hab
  simp only at this
  linarith

/-- The map `u ↦ u e^u + u` is continuous. -/
theorem shiftedMulExp_continuous : Continuous shiftedMulExp :=
  (continuous_id.mul Real.continuous_exp).add continuous_id

/-- The map `u ↦ u e^u + u` sends zero to zero. -/
theorem shiftedMulExp_zero : shiftedMulExp 0 = 0 := by simp [shiftedMulExp]

/-- For nonnegative `u`, one has `u ≤ u e^u + u`. -/
theorem le_shiftedMulExp {u : ℝ} (hu : 0 ≤ u) : u ≤ shiftedMulExp u := by
  unfold shiftedMulExp
  have := mul_nonneg hu (Real.exp_pos u).le
  linarith

/-- Existence of the root `u ∈ [0, z]` of `u e^u + u = z`. -/
theorem exists_shiftedMulExp_eq {z : ℝ} (hz : 0 ≤ z) :
    ∃ u ∈ Icc 0 z, shiftedMulExp u = z := by
  have h := intermediate_value_Icc hz shiftedMulExp_continuous.continuousOn
  exact h ⟨by rw [shiftedMulExp_zero]; exact hz, le_shiftedMulExp hz⟩

/-- The `r = 1` Lambert function: the root `u ≥ 0` of `u e^u + u = z`. -/
noncomputable def shiftedLambertW (z : ℝ) : ℝ :=
  Function.invFunOn shiftedMulExp (Ici 0) z

/-- The shifted Lambert function is nonnegative at every nonnegative argument. -/
theorem shiftedLambertW_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ shiftedLambertW z := by
  obtain ⟨u, hu, huz⟩ := exists_shiftedMulExp_eq hz
  exact mem_Ici.mp (Function.invFunOn_mem ⟨u, mem_Ici.mpr hu.1, huz⟩)

/-- The defining identity `u e^u + u = z`. -/
theorem shiftedMulExp_shiftedLambertW {z : ℝ} (hz : 0 ≤ z) :
    shiftedMulExp (shiftedLambertW z) = z := by
  obtain ⟨u, hu, huz⟩ := exists_shiftedMulExp_eq hz
  exact Function.invFunOn_eq ⟨u, mem_Ici.mpr hu.1, huz⟩

/-- Expanded form of the defining identity `u e^u + u = z`. -/
theorem shiftedLambertW_mul_exp_add {z : ℝ} (hz : 0 ≤ z) :
    shiftedLambertW z * Real.exp (shiftedLambertW z) + shiftedLambertW z = z :=
  shiftedMulExp_shiftedLambertW hz

/-- Uniqueness of the root. -/
theorem shiftedLambertW_unique {z u : ℝ} (hz : 0 ≤ z) (hu : 0 ≤ u)
    (huz : shiftedMulExp u = z) : u = shiftedLambertW z :=
  shiftedMulExp_strictMonoOn.injOn (mem_Ici.mpr hu)
    (mem_Ici.mpr (shiftedLambertW_nonneg hz))
    (by rw [huz, shiftedMulExp_shiftedLambertW hz])

/-- The shifted Lambert function sends zero to zero. -/
theorem shiftedLambertW_zero : shiftedLambertW 0 = 0 :=
  (shiftedLambertW_unique le_rfl le_rfl shiftedMulExp_zero).symm

/-- The shifted Lambert value at a nonnegative argument is at most that argument. -/
theorem shiftedLambertW_le {z : ℝ} (hz : 0 ≤ z) : shiftedLambertW z ≤ z := by
  have := le_shiftedMulExp (shiftedLambertW_nonneg hz)
  rwa [shiftedMulExp_shiftedLambertW hz] at this

/-- The shifted Lambert function is positive at every positive argument. -/
theorem shiftedLambertW_pos {z : ℝ} (hz : 0 < z) : 0 < shiftedLambertW z := by
  rcases (shiftedLambertW_nonneg hz.le).lt_or_eq with h | h
  · exact h
  · have := shiftedMulExp_shiftedLambertW hz.le
    rw [← h, shiftedMulExp_zero] at this
    linarith

/-- `W(u e^u) = u` for `u ≥ 0`. -/
theorem principalLambertW_mul_exp_self {u : ℝ} (hu : 0 ≤ u) :
    principalLambertW (u * Real.exp u) = u :=
  (principalLambertW_unique (neg_exp_neg_one_le_of_nonneg (mul_nonneg hu (Real.exp_pos u).le))
    (by linarith) rfl).symm

/-- The compositional inverse `g(z) = z - u(z)` of `f`. -/
noncomputable def lambertShiftInv (z : ℝ) : ℝ := z - shiftedLambertW z

/-- **The exact inverse**, product form: `g(z) = u e^u`. -/
theorem lambertShiftInv_eq_mul_exp {z : ℝ} (hz : 0 ≤ z) :
    lambertShiftInv z = shiftedLambertW z * Real.exp (shiftedLambertW z) := by
  unfold lambertShiftInv
  have := shiftedLambertW_mul_exp_add hz
  linarith

/-- The inverse shifted Lambert map is nonnegative at every nonnegative argument. -/
theorem lambertShiftInv_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ lambertShiftInv z := by
  rw [lambertShiftInv_eq_mul_exp hz]
  exact mul_nonneg (shiftedLambertW_nonneg hz) (Real.exp_pos _).le

/-- `W(g(z)) = u(z)`. -/
theorem principalLambertW_lambertShiftInv {z : ℝ} (hz : 0 ≤ z) :
    principalLambertW (lambertShiftInv z) = shiftedLambertW z := by
  rw [lambertShiftInv_eq_mul_exp hz, principalLambertW_mul_exp_self (shiftedLambertW_nonneg hz)]

/-- **The exact inverse**: `f(g(z)) = z`. -/
theorem lambertShift_lambertShiftInv {z : ℝ} (hz : 0 ≤ z) :
    lambertShift (lambertShiftInv z) = z := by
  unfold lambertShift
  rw [principalLambertW_lambertShiftInv hz]
  unfold lambertShiftInv
  ring

/-- `f` maps `[0,∞)` onto `[0,∞)`. -/
theorem lambertShift_surjOn : SurjOn lambertShift (Ici 0) (Ici 0) :=
  fun z hz => ⟨lambertShiftInv z, mem_Ici.mpr (lambertShiftInv_nonneg (mem_Ici.mp hz)),
    lambertShift_lambertShiftInv (mem_Ici.mp hz)⟩

/-- `g(f(x)) = x`. -/
theorem lambertShiftInv_lambertShift {x : ℝ} (hx : 0 ≤ x) :
    lambertShiftInv (lambertShift x) = x :=
  lambertShift_strictMonoOn.injOn
    (mem_Ici.mpr (lambertShiftInv_nonneg (lambertShift_nonneg hx))) (mem_Ici.mpr hx)
    (lambertShift_lambertShiftInv (lambertShift_nonneg hx))

/-- The inverse is characterized by the equation: for `x ≥ 0`, `f(x) = z ↔ x = g(z)`. -/
theorem lambertShift_eq_iff {x z : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) :
    lambertShift x = z ↔ x = lambertShiftInv z :=
  ⟨fun h => by rw [← h, lambertShiftInv_lambertShift hx],
   fun h => by rw [h, lambertShift_lambertShiftInv hz]⟩

/-- Upper bracket: `g(z) < z` for `z > 0`. -/
theorem lambertShiftInv_lt_self {z : ℝ} (hz : 0 < z) : lambertShiftInv z < z := by
  unfold lambertShiftInv
  have := shiftedLambertW_pos hz
  linarith

/-- Lower bracket: `z - W(z) < g(z)` for `z > 0`, i.e. `u(z) < W(z)`. -/
theorem shiftedLambertW_lt_principalLambertW {z : ℝ} (hz : 0 < z) :
    shiftedLambertW z < principalLambertW z := by
  have hu := shiftedLambertW_nonneg hz.le
  have hW := principalLambertW_nonneg hz.le
  have hlt : shiftedLambertW z * Real.exp (shiftedLambertW z)
      < principalLambertW z * Real.exp (principalLambertW z) := by
    rw [principalLambertW_mul_exp (neg_exp_neg_one_le_of_nonneg hz.le)]
    have := shiftedLambertW_mul_exp_add hz.le
    have := shiftedLambertW_pos hz
    linarith
  exact (mul_exp_strictMonoOn.lt_iff_lt (mem_Ici.mpr (by linarith))
    (mem_Ici.mpr (by linarith))).mp hlt

/-- Lower bracket for the inverse: `z - W(z) < g(z)` when `z > 0`. -/
theorem sub_principalLambertW_lt_lambertShiftInv {z : ℝ} (hz : 0 < z) :
    z - principalLambertW z < lambertShiftInv z := by
  unfold lambertShiftInv
  have := shiftedLambertW_lt_principalLambertW hz
  linarith

/-! ### The derivative bracket `1 ≤ f' ≤ 2` and the residual certificate -/

/-- Derivative of `f` at `x > 0`. -/
theorem lambertShift_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt lambertShift
      (1 + (Real.exp (principalLambertW x) * (principalLambertW x + 1))⁻¹) x :=
  (hasDerivAt_id x).add (principalLambertW_hasDerivAt (neg_exp_neg_one_lt_of_nonneg hx.le))

/-- `0 < W'(x) ≤ 1` for `x > 0`: the inverse-function derivative is at most `1`. -/
theorem inv_exp_mul_add_one_le_one {x : ℝ} (hx : 0 ≤ x) :
    (Real.exp (principalLambertW x) * (principalLambertW x + 1))⁻¹ ≤ 1 := by
  have hW := principalLambertW_nonneg hx
  have h1 : 1 ≤ Real.exp (principalLambertW x) := Real.one_le_exp hW
  have h2 : 1 ≤ principalLambertW x + 1 := by linarith
  exact inv_le_one_of_one_le₀ (one_le_mul_of_one_le_of_one_le h1 h2)

/-- The derivative of the shifted Lambert map is at least one on `(0,∞)`. -/
theorem one_le_deriv_lambertShift {x : ℝ} (hx : 0 < x) : 1 ≤ deriv lambertShift x := by
  rw [(lambertShift_hasDerivAt hx).deriv]
  have := inv_nonneg.mpr (mul_nonneg (Real.exp_pos (principalLambertW x)).le
    (by linarith [principalLambertW_nonneg hx.le] : (0 : ℝ) ≤ principalLambertW x + 1))
  linarith

/-- The derivative of the shifted Lambert map is at most two on `(0,∞)`. -/
theorem deriv_lambertShift_le_two {x : ℝ} (hx : 0 < x) : deriv lambertShift x ≤ 2 := by
  rw [(lambertShift_hasDerivAt hx).deriv]
  have := inv_exp_mul_add_one_le_one hx.le
  linarith

/-- The shifted Lambert map is differentiable on the interior of `[0,∞)`. -/
theorem lambertShift_differentiableOn : DifferentiableOn ℝ lambertShift (interior (Ici 0)) := by
  rw [interior_Ici]
  exact fun x hx => (lambertShift_hasDerivAt (mem_Ioi.mp hx)).differentiableAt.differentiableWithinAt

/-- Two-sided Lipschitz bracket for `f` on `[0,∞)`, ordered form. -/
theorem sub_le_lambertShift_sub {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    y - x ≤ lambertShift y - lambertShift x := by
  have h := (convex_Ici (0 : ℝ)).mul_sub_le_image_sub_of_le_deriv lambertShift_continuousOn
    lambertShift_differentiableOn
    (fun t ht => one_le_deriv_lambertShift (by rw [interior_Ici] at ht; exact mem_Ioi.mp ht))
    x (mem_Ici.mpr hx) y (mem_Ici.mpr (hx.trans hxy)) hxy
  linarith

/-- Ordered upper Lipschitz bound for the shifted Lambert map on `[0,∞)`. -/
theorem lambertShift_sub_le_two_mul_sub {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    lambertShift y - lambertShift x ≤ 2 * (y - x) :=
  (convex_Ici (0 : ℝ)).image_sub_le_mul_sub_of_deriv_le lambertShift_continuousOn
    lambertShift_differentiableOn
    (fun t ht => deriv_lambertShift_le_two (by rw [interior_Ici] at ht; exact mem_Ioi.mp ht))
    x (mem_Ici.mpr hx) y (mem_Ici.mpr (hx.trans hxy)) hxy

/-- `|x - y| ≤ |f(x) - f(y)|` on `[0,∞)`. -/
theorem abs_sub_le_abs_lambertShift_sub {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |x - y| ≤ |lambertShift x - lambertShift y| := by
  have hderiv : ∀ z ∈ interior (Ici (0 : ℝ)), (1 : ℝ) ≤ deriv lambertShift z := by
    intro z hz
    rw [interior_Ici] at hz
    exact one_le_deriv_lambertShift (mem_Ioi.mp hz)
  have h := mul_abs_sub_le_abs_sub_of_le_deriv (convex_Ici (0 : ℝ))
    lambertShift_continuousOn lambertShift_differentiableOn hderiv
    (mem_Ici.mpr hx) (mem_Ici.mpr hy)
  simpa using h

/-- `|f(x) - f(y)| ≤ 2 |x - y|` on `[0,∞)`, an instance of the general upper
bracket at `m = 1`, `M = 2`. -/
theorem abs_lambertShift_sub_le_two_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |lambertShift x - lambertShift y| ≤ 2 * |x - y| := by
  have hupper : ∀ z ∈ interior (Ici (0 : ℝ)), deriv lambertShift z ≤ 2 := by
    intro z hz
    rw [interior_Ici] at hz
    exact deriv_lambertShift_le_two (mem_Ioi.mp hz)
  have hlower : ∀ z ∈ interior (Ici (0 : ℝ)), (1 : ℝ) ≤ deriv lambertShift z := by
    intro z hz
    rw [interior_Ici] at hz
    exact one_le_deriv_lambertShift (mem_Ioi.mp hz)
  exact abs_sub_le_of_le_deriv (convex_Ici (0 : ℝ)) lambertShift_continuousOn
    lambertShift_differentiableOn hupper hlower zero_le_one
    (mem_Ici.mpr hx) (mem_Ici.mpr hy)

/-- **Residual certificate, upper half**: a candidate `x̃ ≥ 0` with residual
`R = f(x̃) - z` is within `|R|` of the true inverse. -/
theorem abs_sub_lambertShiftInv_le_abs_residual {z x : ℝ} (hz : 0 ≤ z) (hx : 0 ≤ x) :
    |x - lambertShiftInv z| ≤ |lambertShift x - z| := by
  have := abs_sub_le_abs_lambertShift_sub hx (lambertShiftInv_nonneg hz)
  rwa [lambertShift_lambertShiftInv hz] at this

/-- **Residual certificate, lower half**: `|R| ≤ 2 |x̃ - g(z)|`. -/
theorem abs_residual_le_two_mul_abs_sub_lambertShiftInv {z x : ℝ} (hz : 0 ≤ z) (hx : 0 ≤ x) :
    |lambertShift x - z| ≤ 2 * |x - lambertShiftInv z| := by
  have := abs_lambertShift_sub_le_two_mul hx (lambertShiftInv_nonneg hz)
  rwa [lambertShift_lambertShiftInv hz] at this

/-- The residual and the error have the same sign: `0 < f(x̃) - z ↔ g(z) < x̃`. -/
theorem residual_pos_iff {z x : ℝ} (hz : 0 ≤ z) (hx : 0 ≤ x) :
    0 < lambertShift x - z ↔ lambertShiftInv z < x := by
  have h := lambertShift_lambertShiftInv hz
  have hg : lambertShiftInv z ∈ Ici (0 : ℝ) := mem_Ici.mpr (lambertShiftInv_nonneg hz)
  constructor
  · intro hpos
    have hlt : lambertShift (lambertShiftInv z) < lambertShift x := by
      rw [h]
      linarith
    exact (lambertShift_strictMonoOn.lt_iff_lt hg (mem_Ici.mpr hx)).mp hlt
  · intro hlt
    have := lambertShift_strictMonoOn hg (mem_Ici.mpr hx) hlt
    rw [h] at this
    linarith

/-- `f(x̃) - z < 0 ↔ x̃ < g(z)`. -/
theorem residual_neg_iff {z x : ℝ} (hz : 0 ≤ z) (hx : 0 ≤ x) :
    lambertShift x - z < 0 ↔ x < lambertShiftInv z := by
  have h := lambertShift_lambertShiftInv hz
  have hg : lambertShiftInv z ∈ Ici (0 : ℝ) := mem_Ici.mpr (lambertShiftInv_nonneg hz)
  constructor
  · intro hneg
    have hlt : lambertShift x < lambertShift (lambertShiftInv z) := by
      rw [h]
      linarith
    exact (lambertShift_strictMonoOn.lt_iff_lt (mem_Ici.mpr hx) hg).mp hlt
  · intro hlt
    have := lambertShift_strictMonoOn (mem_Ici.mpr hx) hg hlt
    rw [h] at this
    linarith

/-! ### Monotonicity, continuity, and the derivative of the inverse

The drafts' `eq:g-prime-bounds`: on the open half-line `g` is differentiable with
`1/2 < g' < 1`.  Both bounds come from `1 < f' < 2` there, which is the strict
form of the bracket above: `W' = (e^W (W+1))⁻¹` lies strictly between `0` and `1`
once `W > 0`.  (At `z = 0` the one-sided derivative is `1/2`, the endpoint value
the bracket degenerates to; it is not covered here.) -/

/-- `g(z) > 0` for `z > 0`. -/
theorem lambertShiftInv_pos {z : ℝ} (hz : 0 < z) : 0 < lambertShiftInv z := by
  rw [lambertShiftInv_eq_mul_exp hz.le]
  exact mul_pos (shiftedLambertW_pos hz) (Real.exp_pos _)

/-- `f(x) > 0` for `x > 0`. -/
theorem lambertShift_pos {x : ℝ} (hx : 0 < x) : 0 < lambertShift x := by
  have := lambertShift_strictMonoOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx.le) hx
  rwa [lambertShift_zero] at this

/-- `g` is strictly increasing on `[0,∞)`. -/
theorem lambertShiftInv_strictMonoOn : StrictMonoOn lambertShiftInv (Ici 0) := by
  intro a ha b hb hab
  by_contra hcon
  push_neg at hcon
  have h := lambertShift_strictMonoOn.monotoneOn
    (mem_Ici.mpr (lambertShiftInv_nonneg (mem_Ici.mp hb)))
    (mem_Ici.mpr (lambertShiftInv_nonneg (mem_Ici.mp ha))) hcon
  rw [lambertShift_lambertShiftInv (mem_Ici.mp hb),
    lambertShift_lambertShiftInv (mem_Ici.mp ha)] at h
  linarith

/-- `g` maps the open half-line onto itself. -/
theorem lambertShiftInv_image_Ioi : lambertShiftInv '' Ioi 0 = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact lambertShiftInv_pos hz
  · intro hx
    exact ⟨lambertShift x, lambertShift_pos hx, lambertShiftInv_lambertShift hx.le⟩

/-- `g` is continuous at every positive point. -/
theorem lambertShiftInv_continuousAt {z : ℝ} (hz : 0 < z) :
    ContinuousAt lambertShiftInv z := by
  have hmono : StrictMonoOn lambertShiftInv (Ioi 0) :=
    lambertShiftInv_strictMonoOn.mono fun _ h => mem_Ici.mpr (le_of_lt h)
  refine hmono.continuousAt_of_image_mem_nhds (isOpen_Ioi.mem_nhds hz) ?_
  rw [lambertShiftInv_image_Ioi]
  exact Ioi_mem_nhds (lambertShiftInv_pos hz)

/-- The inverse identity holds on a whole neighbourhood of a positive point. -/
theorem lambertShift_lambertShiftInv_eventually {z : ℝ} (hz : 0 < z) :
    ∀ᶠ y in nhds z, lambertShift (lambertShiftInv y) = y := by
  filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
  exact lambertShift_lambertShiftInv (le_of_lt hy)

/-- `0 < W'(x) < 1` for `x > 0`: the inverse-function derivative of `W`. -/
theorem inv_exp_mul_add_one_lt_one {x : ℝ} (hx : 0 < x) :
    (Real.exp (principalLambertW x) * (principalLambertW x + 1))⁻¹ < 1 := by
  have hW : 0 < principalLambertW x := principalLambertW_pos hx
  have h1 : 1 < Real.exp (principalLambertW x) := Real.one_lt_exp_iff.mpr hW
  have h2 : (1 : ℝ) < principalLambertW x + 1 := by linarith
  have : (1 : ℝ) < Real.exp (principalLambertW x) * (principalLambertW x + 1) :=
    one_lt_mul_of_lt_of_le h1 h2.le
  exact inv_lt_one_of_one_lt₀ this

/-- **Inverse-function derivative of `g`.** -/
theorem lambertShiftInv_hasDerivAt {z : ℝ} (hz : 0 < z) :
    HasDerivAt lambertShiftInv
      (1 + (Real.exp (principalLambertW (lambertShiftInv z)) *
        (principalLambertW (lambertShiftInv z) + 1))⁻¹)⁻¹ z := by
  have hgz : 0 < lambertShiftInv z := lambertShiftInv_pos hz
  have hpos : 0 < (Real.exp (principalLambertW (lambertShiftInv z)) *
      (principalLambertW (lambertShiftInv z) + 1))⁻¹ :=
    inv_pos.mpr (mul_pos (Real.exp_pos _)
      (by linarith [principalLambertW_nonneg hgz.le]))
  refine HasDerivAt.of_local_left_inverse (lambertShiftInv_continuousAt hz)
    (lambertShift_hasDerivAt hgz) (by positivity)
    (lambertShift_lambertShiftInv_eventually hz)

/-- **`eq:g-prime-bounds`, upper half**: `g'(z) < 1` for `z > 0`. -/
theorem deriv_lambertShiftInv_lt_one {z : ℝ} (hz : 0 < z) :
    deriv lambertShiftInv z < 1 := by
  have hgz : 0 < lambertShiftInv z := lambertShiftInv_pos hz
  rw [(lambertShiftInv_hasDerivAt hz).deriv]
  have hpos : 0 < (Real.exp (principalLambertW (lambertShiftInv z)) *
      (principalLambertW (lambertShiftInv z) + 1))⁻¹ :=
    inv_pos.mpr (mul_pos (Real.exp_pos _)
      (by linarith [principalLambertW_nonneg hgz.le]))
  exact inv_lt_one_of_one_lt₀ (by linarith)

/-- **`eq:g-prime-bounds`, lower half**: `1/2 < g'(z)` for `z > 0`. -/
theorem half_lt_deriv_lambertShiftInv {z : ℝ} (hz : 0 < z) :
    1 / 2 < deriv lambertShiftInv z := by
  have hgz : 0 < lambertShiftInv z := lambertShiftInv_pos hz
  rw [(lambertShiftInv_hasDerivAt hz).deriv]
  have hlt : (Real.exp (principalLambertW (lambertShiftInv z)) *
      (principalLambertW (lambertShiftInv z) + 1))⁻¹ < 1 :=
    inv_exp_mul_add_one_lt_one hgz
  have hpos : 0 < (Real.exp (principalLambertW (lambertShiftInv z)) *
      (principalLambertW (lambertShiftInv z) + 1))⁻¹ :=
    inv_pos.mpr (mul_pos (Real.exp_pos _)
      (by linarith [principalLambertW_nonneg hgz.le]))
  rw [lt_inv_comm₀ (by norm_num) (by linarith)]
  linarith

/-- The two bounds together, the drafts' `eq:g-prime-bounds` on the open half-line. -/
theorem deriv_lambertShiftInv_bounds {z : ℝ} (hz : 0 < z) :
    1 / 2 < deriv lambertShiftInv z ∧ deriv lambertShiftInv z < 1 :=
  ⟨half_lt_deriv_lambertShiftInv hz, deriv_lambertShiftInv_lt_one hz⟩

/-! ### Concavity of `f` and convexity of `g`

The drafts observe that `W'' < 0` makes `f` concave and therefore `g` convex.
The corpus already has the strict concavity of the branch
(`strictConcaveOn_principalLambertW`); here the consequence for `g` is taken
from the derivative instead, since `g' = (1 + W'(g))⁻¹` is strictly increasing
as soon as `W'` is strictly decreasing. -/

/-- `W'` is strictly decreasing on `[0,∞)`: the inverse-function derivative
`(e^{W}(W+1))⁻¹` falls as `W` rises. -/
theorem inv_exp_mul_add_one_strictAntiOn :
    StrictAntiOn (fun x : ℝ => (Real.exp (principalLambertW x) *
      (principalLambertW x + 1))⁻¹) (Ici 0) := by
  intro a ha b hb hab
  have hWa : 0 ≤ principalLambertW a := principalLambertW_nonneg (mem_Ici.mp ha)
  have hWab : principalLambertW a < principalLambertW b :=
    principalLambertW_strictMonoOn
      (mem_Ici.mpr (neg_exp_neg_one_le_of_nonneg (mem_Ici.mp ha)))
      (mem_Ici.mpr (neg_exp_neg_one_le_of_nonneg (mem_Ici.mp hb))) hab
  have hexp : Real.exp (principalLambertW a) < Real.exp (principalLambertW b) :=
    Real.exp_lt_exp.mpr hWab
  have hlin : principalLambertW a + 1 < principalLambertW b + 1 := by linarith
  have hprod : Real.exp (principalLambertW a) * (principalLambertW a + 1) <
      Real.exp (principalLambertW b) * (principalLambertW b + 1) :=
    mul_lt_mul'' hexp hlin (Real.exp_pos _).le (by linarith)
  have hpos : 0 < Real.exp (principalLambertW a) * (principalLambertW a + 1) :=
    mul_pos (Real.exp_pos _) (by linarith)
  simpa only [one_div] using one_div_lt_one_div_of_lt hpos hprod

/-- `g'` is strictly increasing on the open half-line. -/
theorem deriv_lambertShiftInv_strictMonoOn :
    StrictMonoOn (deriv lambertShiftInv) (Ioi 0) := by
  intro a ha b hb hab
  have ha0 : 0 < a := mem_Ioi.mp ha
  have hb0 : 0 < b := mem_Ioi.mp hb
  rw [(lambertShiftInv_hasDerivAt ha0).deriv, (lambertShiftInv_hasDerivAt hb0).deriv]
  have hga : 0 < lambertShiftInv a := lambertShiftInv_pos ha0
  have hgab : lambertShiftInv a < lambertShiftInv b :=
    lambertShiftInv_strictMonoOn (mem_Ici.mpr ha0.le) (mem_Ici.mpr hb0.le) hab
  have hanti := inv_exp_mul_add_one_strictAntiOn (mem_Ici.mpr hga.le)
    (mem_Ici.mpr (lambertShiftInv_pos hb0).le) hgab
  simp only at hanti
  have hposb : 0 < (Real.exp (principalLambertW (lambertShiftInv b)) *
      (principalLambertW (lambertShiftInv b) + 1))⁻¹ :=
    inv_pos.mpr (mul_pos (Real.exp_pos _)
      (by linarith [principalLambertW_nonneg (lambertShiftInv_pos hb0).le]))
  have h1 : (0 : ℝ) < 1 + (Real.exp (principalLambertW (lambertShiftInv b)) *
      (principalLambertW (lambertShiftInv b) + 1))⁻¹ := by linarith
  simpa only [one_div] using one_div_lt_one_div_of_lt h1 (by linarith)

/-- **The inverse is strictly convex** on the open half-line, the drafts'
counterpart of the concavity of `f`. -/
theorem strictConvexOn_lambertShiftInv :
    StrictConvexOn ℝ (Ioi 0) lambertShiftInv := by
  refine StrictMonoOn.strictConvexOn_of_deriv (convex_Ioi 0)
    (fun z hz => (lambertShiftInv_continuousAt (mem_Ioi.mp hz)).continuousWithinAt) ?_
  rw [interior_Ioi]
  exact deriv_lambertShiftInv_strictMonoOn

end Fabius
