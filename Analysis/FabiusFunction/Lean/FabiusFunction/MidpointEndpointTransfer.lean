import FabiusFunction.BoundedDerivatives
import FabiusFunction.Monotonicity
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Exact transfer between the endpoint and the midpoint

The Fabius differential equation and reflection symmetry combine particularly
cleanly on the two half-cells adjacent to the midpoint.  For
`0 ≤ h ≤ 1 / 2`, the sum

`F(1 / 2 + h) + F(h)`

has constant derivative `2` and initial value `1 / 2`.  This gives the exact
midpoint--endpoint transmutation

`F(1 / 2 + h) = 1 / 2 + 2 * h - F(h)`.

Reflection gives the companion formula on the left of the midpoint.  The same
calculation also transfers the first jet, while the global iterated-derivative
formula shows that every midpoint jet of order at least two vanishes.  No
analytic continuation or Taylor expansion is used.

The pointwise transmutation also settles the draft's central integral
consequences.  For every real oriented radius, the midpoint-centered
oriented integral equals that radius; hence every nondegenerate ordinary
centered interval has average `1 / 2`.  More generally, an arbitrary weight
transports the right and left midpoint defects to the signed endpoint germ;
the Cauchy kernels for all anchored repeated primitives follow at once.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-- **Exact midpoint--endpoint transmutation.**  On the whole closed half-cell
`0 ≤ h ≤ 1 / 2`, translating the endpoint germ to the right of the
midpoint turns it into its affine complement:

`F(1 / 2 + h) = 1 / 2 + 2 * h - F(h)`.

The proof differentiates `F(1 / 2 + h) + F(h)`.  The two Fabius derivative
equations sample `F(1 - 2 * h)` and `F(2 * h)`, whose sum is one by reflection,
so the derivative is exactly two. -/
theorem fabiusReal_midpoint_add_eq
    (F : BoundedFabius) (hF : IsFabius F) {h : ℝ}
    (hh0 : 0 ≤ h) (hhhalf : h ≤ 1 / 2) :
    fabiusReal F (1 / 2 + h) = 1 / 2 + 2 * h - fabiusReal F h := by
  let lhs : ℝ → ℝ := fun t =>
    fabiusReal F (1 / 2 + t) + fabiusReal F t
  let rhs : ℝ → ℝ := fun t => 1 / 2 + 2 * t
  have hlhsContinuous : Continuous lhs := by
    dsimp only [lhs]
    exact ((hF.contDiff.continuous.comp
      (continuous_const.add continuous_id))).add hF.contDiff.continuous
  have hrhsContinuous : Continuous rhs := by
    dsimp only [rhs]
    fun_prop
  have hlhsDeriv : ∀ t ∈ Ico (0 : ℝ) (1 / 2),
      HasDerivWithinAt lhs 2 (Ici t) t := by
    intro t ht
    have htclosed : t ∈ Icc (0 : ℝ) (1 / 2) := ⟨ht.1, ht.2.le⟩
    have hshift : HasDerivAt (fun z : ℝ => fabiusReal F (1 / 2 + z))
        (2 * fabiusReal F (1 - 2 * t)) t := by
      have hhigh := fabius_hasDerivAt_reflected_of_half_le F hF
        (t := 1 / 2 + t) (le_add_of_nonneg_right ht.1)
      have hhigh' : HasDerivAt (fabiusReal F)
          (2 * fabiusReal F (1 - 2 * t)) (1 / 2 + t) := by
        convert hhigh using 1
        ring
      have hcomp := hhigh'.comp t
        ((hasDerivAt_id t).const_add (1 / 2 : ℝ))
      simpa [Function.comp_def] using hcomp
    have hlow := hF.hasDerivAt t htclosed
    have hsum : HasDerivAt lhs
        (2 * fabiusReal F (1 - 2 * t) + 2 * fabiusReal F (2 * t)) t := by
      simpa only [lhs, Pi.add_apply] using hshift.fun_add hlow
    have hsymmetry :
        fabiusReal F (1 - 2 * t) = 1 - fabiusReal F (2 * t) :=
      hF.symmetry (2 * t)
        ⟨mul_nonneg (by norm_num) ht.1, by nlinarith [ht.2.le]⟩
    have hcoefficient :
        2 * fabiusReal F (1 - 2 * t) + 2 * fabiusReal F (2 * t) = 2 := by
      rw [hsymmetry]
      ring
    exact (hsum.congr_deriv hcoefficient).hasDerivWithinAt
  have hrhsDeriv : ∀ t ∈ Ico (0 : ℝ) (1 / 2),
      HasDerivWithinAt rhs 2 (Ici t) t := by
    intro t _ht
    have hderiv : HasDerivAt rhs 2 t := by
      dsimp only [rhs]
      simpa using
        (((hasDerivAt_id t).const_mul (2 : ℝ)).const_add (1 / 2 : ℝ))
    exact hderiv.hasDerivWithinAt
  have hinitial : lhs 0 = rhs 0 := by
    dsimp only [lhs, rhs]
    rw [add_zero, hF.zero_of_nonpos 0 le_rfl, add_zero, mul_zero, add_zero,
      fabius_half F hF]
  have heq : lhs h = rhs h :=
    eq_of_has_deriv_right_eq hlhsDeriv hrhsDeriv
      hlhsContinuous.continuousOn hrhsContinuous.continuousOn hinitial h
      ⟨hh0, hhhalf⟩
  dsimp only [lhs, rhs] at heq
  linarith

/-- **Reflected midpoint--endpoint transmutation.**  On the same closed
half-cell, the value to the left of the midpoint is the affine translate of
the endpoint value:

`F(1 / 2 - h) = 1 / 2 - 2 * h + F(h)`.

This is the reflection of `fabiusReal_midpoint_add_eq`; no second integration
argument is needed. -/
theorem fabiusReal_midpoint_sub_eq
    (F : BoundedFabius) (hF : IsFabius F) {h : ℝ}
    (hh0 : 0 ≤ h) (hhhalf : h ≤ 1 / 2) :
    fabiusReal F (1 / 2 - h) = 1 / 2 - 2 * h + fabiusReal F h := by
  calc
    fabiusReal F (1 / 2 - h) =
        1 - fabiusReal F (1 / 2 + h) := by
      convert hF.symmetry_all (1 / 2 + h) using 1 <;> ring
    _ = 1 / 2 - 2 * h + fabiusReal F h := by
      rw [fabiusReal_midpoint_add_eq F hF hh0 hhhalf]
      ring

/-- **First-jet transfer to the right of the midpoint.**  For
`0 ≤ h ≤ 1 / 2`, the endpoint and translated midpoint derivatives add to
two:

`F'(1 / 2 + h) = 2 - F'(h)`.

Unlike a formal differentiation of the preceding value identity, this proof
uses the two already-established pointwise derivative formulas directly, so
it includes both endpoints of the half-cell. -/
theorem deriv_fabiusReal_midpoint_add_eq
    (F : BoundedFabius) (hF : IsFabius F) {h : ℝ}
    (hh0 : 0 ≤ h) (hhhalf : h ≤ 1 / 2) :
    deriv (fabiusReal F) (1 / 2 + h) =
      2 - deriv (fabiusReal F) h := by
  have hhigh := fabius_hasDerivAt_reflected_of_half_le F hF
    (t := 1 / 2 + h) (by linarith : 1 / 2 ≤ 1 / 2 + h)
  have hlow := hF.hasDerivAt h ⟨hh0, hhhalf⟩
  have hreflection :
      fabiusReal F (1 - 2 * h) = 1 - fabiusReal F (2 * h) :=
    hF.symmetry (2 * h) ⟨by linarith, by linarith⟩
  rw [hhigh.deriv, hlow.deriv,
    show 2 - 2 * (1 / 2 + h) = 1 - 2 * h by ring, hreflection]
  ring

/-- **First-jet transfer to the left of the midpoint.**  Reflection does not
change the first-jet complement: throughout `0 ≤ h ≤ 1 / 2`,

`F'(1 / 2 - h) = 2 - F'(h)`.

Both sides of the midpoint therefore have the same derivative at equal
distance from it, as expected from the symmetry of the bounded Fabius
function. -/
theorem deriv_fabiusReal_midpoint_sub_eq
    (F : BoundedFabius) (hF : IsFabius F) {h : ℝ}
    (hh0 : 0 ≤ h) (hhhalf : h ≤ 1 / 2) :
    deriv (fabiusReal F) (1 / 2 - h) =
      2 - deriv (fabiusReal F) h := by
  calc
    deriv (fabiusReal F) (1 / 2 - h) =
        deriv (fabiusReal F) (1 / 2 + h) := by
      convert deriv_fabiusReal_one_sub F hF (1 / 2 + h) using 1 <;> ring
    _ = 2 - deriv (fabiusReal F) h :=
      deriv_fabiusReal_midpoint_add_eq F hF hh0 hhhalf

/-- Every midpoint jet of order at least two vanishes.  The below-one bounded
derivative formula inherited from the global signed-extension formula samples
the extension at `2 ^ k * (1 / 2) = 2 ^ (k - 1)`; for `k ≥ 2` this is an even
integer grid point, where the signed extension is zero. -/
theorem iteratedDeriv_fabiusReal_half_eq_zero_of_two_le
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (hk : 2 ≤ k) :
    iteratedDeriv k (fabiusReal F) (1 / 2) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 2 := ⟨k - 2, by omega⟩
  rw [iteratedDeriv_fabiusReal_of_lt_one F hF (j + 2) (by norm_num)]
  have hargument :
      (2 : ℝ) ^ (j + 2) * (1 / 2) =
        2 * ((2 ^ j : ℕ) : ℝ) := by
    push_cast
    rw [pow_add]
    norm_num
    ring
  rw [hargument, extendedFabius_two_mul_nat F hF, mul_zero]

/-! ## Integral and repeated-primitive transfer -/

/-- **Exact oriented integral of every midpoint-centered interval.**  For
every real oriented radius `a`,

`∫ x in 1 / 2 - a..1 / 2 + a, F(x) = a`.

Thus an ordinary symmetric interval of positive radius has average `1 / 2`.
The theorem is stronger than the nonnegative half-cell form: global
reflection symmetry and oriented interval integration make the displayed
identity valid for all real `a`. -/
theorem intervalIntegral_fabiusReal_centered
    (F : BoundedFabius) (hF : IsFabius F) (a : ℝ) :
    (∫ x in (1 / 2 : ℝ) - a..(1 / 2 : ℝ) + a, fabiusReal F x) = a := by
  have hreflect :
      (∫ x in (1 / 2 : ℝ) - a..(1 / 2 : ℝ) + a,
          fabiusReal F (1 - x)) =
        ∫ x in (1 / 2 : ℝ) - a..(1 / 2 : ℝ) + a,
          fabiusReal F x := by
    have h := intervalIntegral.integral_comp_sub_left
      (f := fabiusReal F)
      (a := (1 / 2 : ℝ) - a)
      (b := (1 / 2 : ℝ) + a) 1
    convert h using 1 <;> ring
  have hsymm :
      (∫ x in (1 / 2 : ℝ) - a..(1 / 2 : ℝ) + a,
          fabiusReal F (1 - x)) =
        ∫ x in (1 / 2 : ℝ) - a..(1 / 2 : ℝ) + a,
          (1 - fabiusReal F x) :=
    intervalIntegral.integral_congr
      (fun x _hx => hF.symmetry_all x)
  rw [hreflect] at hsymm
  have hint :
      IntervalIntegrable (fabiusReal F) MeasureTheory.volume
        ((1 / 2 : ℝ) - a) ((1 / 2 : ℝ) + a) :=
    hF.contDiff.continuous.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub intervalIntegrable_const hint] at hsymm
  simp [intervalIntegral.integral_const] at hsymm
  linarith

/-- **Weighted right midpoint-defect transfer.**  On the closed half-cell,
every weighted interval integral of the right midpoint defect is the negative
of the same weighted endpoint integral.  No regularity or integrability
assumption on the weight is needed, because the integrands agree pointwise. -/
theorem intervalIntegral_mul_fabiusReal_midpoint_add_defect_eq_neg
    (F : BoundedFabius) (hF : IsFabius F)
    (w : ℝ → ℝ) (a : ℝ) (ha0 : 0 ≤ a) (hahalf : a ≤ 1 / 2) :
    (∫ h in (0 : ℝ)..a,
      w h * (fabiusReal F (1 / 2 + h) - 1 / 2 - 2 * h)) =
      -(∫ h in (0 : ℝ)..a, w h * fabiusReal F h) := by
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro h hh
  rw [uIcc_of_le ha0] at hh
  change w h * (fabiusReal F (1 / 2 + h) - 1 / 2 - 2 * h) =
    -(w h * fabiusReal F h)
  rw [fabiusReal_midpoint_add_eq F hF hh.1 (hh.2.trans hahalf)]
  ring

/-- **Weighted left midpoint-defect transfer.**  The companion defect to the
left of the midpoint transports the endpoint germ with positive sign. -/
theorem intervalIntegral_mul_fabiusReal_midpoint_sub_defect_eq
    (F : BoundedFabius) (hF : IsFabius F)
    (w : ℝ → ℝ) (a : ℝ) (ha0 : 0 ≤ a) (hahalf : a ≤ 1 / 2) :
    (∫ h in (0 : ℝ)..a,
      w h * (fabiusReal F (1 / 2 - h) - 1 / 2 + 2 * h)) =
      ∫ h in (0 : ℝ)..a, w h * fabiusReal F h := by
  apply intervalIntegral.integral_congr
  intro h hh
  rw [uIcc_of_le ha0] at hh
  change w h * (fabiusReal F (1 / 2 - h) - 1 / 2 + 2 * h) =
    w h * fabiusReal F h
  rw [fabiusReal_midpoint_sub_eq F hF hh.1 (hh.2.trans hahalf)]
  ring

/-- The frontier report's unweighted central-defect identity: its integral
is exactly the negative endpoint mass. -/
theorem intervalIntegral_fabiusReal_midpoint_add_defect_eq_neg
    (F : BoundedFabius) (hF : IsFabius F)
    (a : ℝ) (ha0 : 0 ≤ a) (hahalf : a ≤ 1 / 2) :
    (∫ h in (0 : ℝ)..a,
      (fabiusReal F (1 / 2 + h) - 1 / 2 - 2 * h)) =
      -(∫ h in (0 : ℝ)..a, fabiusReal F h) := by
  simpa only [one_mul] using
    intervalIntegral_mul_fabiusReal_midpoint_add_defect_eq_neg
      F hF (fun _ : ℝ => 1) a ha0 hahalf

/-- **All repeated-primitive kernels at once.**  The Cauchy kernel of every
anchored repeated primitive transports the right midpoint defect to the
negative endpoint germ.  Exponent `n` is the kernel for the `(n + 1)`-fold
anchored primitive. -/
theorem
    intervalIntegral_repeatedPrimitiveKernel_fabiusReal_midpoint_add_defect_eq_neg
    (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (a : ℝ) (ha0 : 0 ≤ a) (hahalf : a ≤ 1 / 2) :
    (∫ h in (0 : ℝ)..a,
      ((a - h) ^ n / (n.factorial : ℝ)) *
        (fabiusReal F (1 / 2 + h) - 1 / 2 - 2 * h)) =
      -(∫ h in (0 : ℝ)..a,
        ((a - h) ^ n / (n.factorial : ℝ)) * fabiusReal F h) :=
  intervalIntegral_mul_fabiusReal_midpoint_add_defect_eq_neg
    F hF (fun h => (a - h) ^ n / (n.factorial : ℝ))
    a ha0 hahalf

end Fabius
