import FabiusFunction.LambertWElementaryBounds

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
-/

set_option autoImplicit false

namespace Fabius

open Set

/-- The shifted Lambert map `f(x) = x + W(x)`. -/
noncomputable def lambertShift (x : ℝ) : ℝ := x + principalLambertW x

/-- `u e^u + u`, whose inverse on `[0,∞)` is the `r = 1` Lambert function. -/
noncomputable def shiftedMulExp (u : ℝ) : ℝ := u * Real.exp u + u

theorem neg_exp_neg_one_le_of_nonneg {x : ℝ} (hx : 0 ≤ x) : -Real.exp (-1) ≤ x := by
  have := Real.exp_pos (-1)
  linarith

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

theorem lambertShift_continuousOn : ContinuousOn lambertShift (Ici 0) :=
  continuousOn_id.add (principalLambertW_continuousOn_Ici.mono
    fun _ hx => mem_Ici.mpr (neg_exp_neg_one_le_of_nonneg hx))

theorem lambertShift_zero : lambertShift 0 = 0 := by
  unfold lambertShift
  have h := principalLambertW_unique (z := 0) (w := 0) (neg_exp_neg_one_le_of_nonneg le_rfl)
    (by norm_num) (by simp)
  rw [← h]
  simp

theorem lambertShift_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ lambertShift x := by
  unfold lambertShift
  have := principalLambertW_nonneg hx
  linarith

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

theorem shiftedMulExp_continuous : Continuous shiftedMulExp :=
  (continuous_id.mul Real.continuous_exp).add continuous_id

theorem shiftedMulExp_zero : shiftedMulExp 0 = 0 := by simp [shiftedMulExp]

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

theorem shiftedLambertW_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ shiftedLambertW z := by
  obtain ⟨u, hu, huz⟩ := exists_shiftedMulExp_eq hz
  exact mem_Ici.mp (Function.invFunOn_mem ⟨u, mem_Ici.mpr hu.1, huz⟩)

/-- The defining identity `u e^u + u = z`. -/
theorem shiftedMulExp_shiftedLambertW {z : ℝ} (hz : 0 ≤ z) :
    shiftedMulExp (shiftedLambertW z) = z := by
  obtain ⟨u, hu, huz⟩ := exists_shiftedMulExp_eq hz
  exact Function.invFunOn_eq ⟨u, mem_Ici.mpr hu.1, huz⟩

theorem shiftedLambertW_mul_exp_add {z : ℝ} (hz : 0 ≤ z) :
    shiftedLambertW z * Real.exp (shiftedLambertW z) + shiftedLambertW z = z :=
  shiftedMulExp_shiftedLambertW hz

/-- Uniqueness of the root. -/
theorem shiftedLambertW_unique {z u : ℝ} (hz : 0 ≤ z) (hu : 0 ≤ u)
    (huz : shiftedMulExp u = z) : u = shiftedLambertW z :=
  shiftedMulExp_strictMonoOn.injOn (mem_Ici.mpr hu)
    (mem_Ici.mpr (shiftedLambertW_nonneg hz))
    (by rw [huz, shiftedMulExp_shiftedLambertW hz])

theorem shiftedLambertW_zero : shiftedLambertW 0 = 0 :=
  (shiftedLambertW_unique le_rfl le_rfl shiftedMulExp_zero).symm

theorem shiftedLambertW_le {z : ℝ} (hz : 0 ≤ z) : shiftedLambertW z ≤ z := by
  have := le_shiftedMulExp (shiftedLambertW_nonneg hz)
  rwa [shiftedMulExp_shiftedLambertW hz] at this

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

theorem one_le_deriv_lambertShift {x : ℝ} (hx : 0 < x) : 1 ≤ deriv lambertShift x := by
  rw [(lambertShift_hasDerivAt hx).deriv]
  have := inv_nonneg.mpr (mul_nonneg (Real.exp_pos (principalLambertW x)).le
    (by linarith [principalLambertW_nonneg hx.le] : (0 : ℝ) ≤ principalLambertW x + 1))
  linarith

theorem deriv_lambertShift_le_two {x : ℝ} (hx : 0 < x) : deriv lambertShift x ≤ 2 := by
  rw [(lambertShift_hasDerivAt hx).deriv]
  have := inv_exp_mul_add_one_le_one hx.le
  linarith

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

theorem lambertShift_sub_le_two_mul_sub {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    lambertShift y - lambertShift x ≤ 2 * (y - x) :=
  (convex_Ici (0 : ℝ)).image_sub_le_mul_sub_of_deriv_le lambertShift_continuousOn
    lambertShift_differentiableOn
    (fun t ht => deriv_lambertShift_le_two (by rw [interior_Ici] at ht; exact mem_Ioi.mp ht))
    x (mem_Ici.mpr hx) y (mem_Ici.mpr (hx.trans hxy)) hxy

/-- `|x - y| ≤ |f(x) - f(y)|` on `[0,∞)`. -/
theorem abs_sub_le_abs_lambertShift_sub {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |x - y| ≤ |lambertShift x - lambertShift y| := by
  rcases le_total x y with h | h
  · have := sub_le_lambertShift_sub hx h
    rw [abs_sub_comm x y, abs_sub_comm (lambertShift x), abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    exact this
  · have := sub_le_lambertShift_sub hy h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact this

/-- `|f(x) - f(y)| ≤ 2 |x - y|` on `[0,∞)`. -/
theorem abs_lambertShift_sub_le_two_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |lambertShift x - lambertShift y| ≤ 2 * |x - y| := by
  rcases le_total x y with h | h
  · have := lambertShift_sub_le_two_mul_sub hx h
    have h' := sub_le_lambertShift_sub hx h
    rw [abs_sub_comm x y, abs_sub_comm (lambertShift x), abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    exact this
  · have := lambertShift_sub_le_two_mul_sub hy h
    have h' := sub_le_lambertShift_sub hy h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact this

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

end Fabius
