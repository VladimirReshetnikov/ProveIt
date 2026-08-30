import FabiusFunction.InverseLayerCake
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Order.ProjIcc

/-!
# An absolutely-continuous calculus for inverse pairs

This module combines the weighted inverse layer-cake theorem with the
fundamental theorem of calculus for absolutely continuous functions.  The
result is a two-function integration identity for an abstract pair of clocks
on arbitrary ordered compact intervals:

`∫ A'(x) B(C(x)) dx + ∫ A(Q(u)) B'(u) du
  = A(b) B(d) - A(a) B(c)`.

Only the inverse-order relation `C x < u ↔ x < Q u` is used.  In particular,
no derivative, Jacobian, global inverse equation, or measurability assumption
is required for either clock.  The order relation is precisely a Galois
connection between the interval restrictions, hence forces both clocks to be
monotone there.  Canonical clamped extensions are used only to certify the
integrability of the two composite products; the layer-cake theorem itself
already hides its measurable extension.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace Fabius

/-- **Two-function absolutely-continuous identity for an inverse pair.**
Suppose `C` maps `[a,b]` into `[c,d]`, `Q` maps `[c,d]` into `[a,b]`, and

`C x < u ↔ x < Q u`

throughout the rectangle.  If `A` and `B` are absolutely continuous on the
respective source and level intervals, then

`∫ₐᵇ A'(x) B(C(x)) dx + ∫_c^d A(Q(u)) B'(u) du
  = A(b) B(d) - A(a) B(c)`.

The assumptions `a ≤ b` and `c ≤ d` choose the orientation of the rectangle
used by the inverse layer-cake theorem.  Equality is allowed in either one,
so all degenerate endpoint cases are included.  Reversed endpoints should be
handled by first swapping the corresponding interval; merely reversing an
interval integral would not reverse the strict order equivalence.

Neither clock is assumed globally measurable.  Their restricted Galois
connection supplies monotonicity, and `IccExtend` constructs canonical
measurable clamped versions for the composite-integrability argument.  Thus
values of `C` and `Q` outside the two closed intervals play no role. -/
theorem intervalIntegral_deriv_mul_comp_add_comp_mul_deriv_of_lt_iff_lt
    (C Q : ℝ → ℝ)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hC : MapsTo C (Icc a b) (Icc c d))
    (hQ : MapsTo Q (Icc c d) (Icc a b))
    (hinv : ∀ ⦃x u : ℝ⦄, x ∈ Icc a b → u ∈ Icc c d →
      (C x < u ↔ x < Q u))
    (A B : ℝ → ℝ)
    (hA : AbsolutelyContinuousOnInterval A a b)
    (hB : AbsolutelyContinuousOnInterval B c d) :
    (∫ x in a..b, deriv A x * B (C x)) +
      (∫ u in c..d, A (Q u) * deriv B u) =
        A b * B d - A a * B c := by
  classical
  -- The strict order equivalence is a Galois connection on the interval
  -- restrictions, so both monotonicity facts are immediate adjoint laws.
  have hgc := galoisConnection_Icc_restrict_of_lt_iff_lt C Q hC hQ hinv
  have hCsubmono : Monotone (fun x : Icc a b ↦ C x) := by
    intro x y hxy
    exact hgc.monotone_u hxy
  have hQsubmono : Monotone (fun u : Icc c d ↦ Q u) := by
    intro u v huv
    exact hgc.monotone_l huv

  let Cext : ℝ → ℝ := IccExtend hab (fun x : Icc a b ↦ C x)
  let Qext : ℝ → ℝ := IccExtend hcd (fun u : Icc c d ↦ Q u)
  have hCextm : Measurable Cext := by
    change Measurable (IccExtend hab (fun x : Icc a b ↦ C x))
    exact (hCsubmono.IccExtend hab).measurable
  have hQextm : Measurable Qext := by
    change Measurable (IccExtend hcd (fun u : Icc c d ↦ Q u))
    exact (hQsubmono.IccExtend hcd).measurable
  have hCext_eq (x : ℝ) (hx : x ∈ Icc a b) : Cext x = C x := by
    change IccExtend hab (fun z : Icc a b ↦ C z) x = C x
    simpa using IccExtend_of_mem hab (fun z : Icc a b ↦ C z) hx
  have hQext_eq (u : ℝ) (hu : u ∈ Icc c d) : Qext u = Q u := by
    change IccExtend hcd (fun z : Icc c d ↦ Q z) u = Q u
    simpa using IccExtend_of_mem hcd (fun z : Icc c d ↦ Q z) hu

  have hAcont : ContinuousOn A (Icc a b) := by
    simpa only [uIcc_of_le hab] using hA.continuousOn
  have hBcont : ContinuousOn B (Icc c d) := by
    simpa only [uIcc_of_le hcd] using hB.continuousOn
  have hAderiv : IntervalIntegrable (deriv A) volume a b :=
    hA.intervalIntegrable_deriv
  have hBderiv : IntervalIntegrable (deriv B) volume c d :=
    hB.intervalIntegrable_deriv

  -- Extend `A` measurably by zero.  On the level interval, composing this
  -- extension with `Q` is exactly `A ∘ Q` and remains uniformly bounded.
  let Aext : ℝ → ℝ := (Icc a b).piecewise A (fun _ ↦ 0)
  have hAextm : Measurable Aext :=
    hAcont.measurable_piecewise continuousOn_const measurableSet_Icc
  obtain ⟨MA, hMA⟩ := hA.exists_bound
  have hAderivOn : Integrable (deriv A) (volume.restrict (Icc a b)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hAderiv
  have hBderivOn : Integrable (deriv B) (volume.restrict (Icc c d)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hcd).mp hBderiv
  have hAQextMeas :
      AEStronglyMeasurable (fun u ↦ Aext (Qext u))
        (volume.restrict (Icc c d)) :=
    (hAextm.comp hQextm).aestronglyMeasurable
  have hAQextBound :
      ∀ᵐ u ∂volume.restrict (Icc c d), ‖Aext (Qext u)‖ ≤ MA := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hQu := hQ hu
    rw [hQext_eq u hu,
      show Aext (Q u) = A (Q u) by simp [Aext, hQu]]
    exact hMA (Q u) (by simpa only [uIcc_of_le hab] using hQu)
  have hAQextDerivOn :
      Integrable (fun u ↦ Aext (Qext u) * deriv B u)
        (volume.restrict (Icc c d)) :=
    hBderivOn.bdd_mul hAQextMeas hAQextBound
  have hAQderivOn :
      Integrable (fun u ↦ A (Q u) * deriv B u)
        (volume.restrict (Icc c d)) := by
    refine hAQextDerivOn.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [hQext_eq u hu,
      show Aext (Q u) = A (Q u) by simp [Aext, hQ hu]]
  have hAQderiv :
      IntervalIntegrable (fun u ↦ A (Q u) * deriv B u) volume c d :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hcd).mpr hAQderivOn

  -- Extend `B` measurably by zero and use the measurable clamped clock.  Its
  -- compact-interval bound turns the integrable derivative of `A` into the
  -- first composite integrand of the claimed identity.
  let Bext : ℝ → ℝ := (Icc c d).piecewise B (fun _ ↦ 0)
  have hBextm : Measurable Bext :=
    hBcont.measurable_piecewise continuousOn_const measurableSet_Icc
  obtain ⟨MB, hMB⟩ := hB.exists_bound
  have hBCextMeas :
      AEStronglyMeasurable (fun x ↦ Bext (Cext x))
        (volume.restrict (Icc a b)) :=
    (hBextm.comp hCextm).aestronglyMeasurable
  have hBCextBound :
      ∀ᵐ x ∂volume.restrict (Icc a b), ‖Bext (Cext x)‖ ≤ MB := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hCx := hC hx
    rw [hCext_eq x hx,
      show Bext (C x) = B (C x) by simp [Bext, hCx]]
    exact hMB (C x) (by simpa only [uIcc_of_le hcd] using hCx)
  have hderivBCextOn :
      Integrable (fun x ↦ deriv A x * Bext (Cext x))
        (volume.restrict (Icc a b)) :=
    hAderivOn.mul_bdd hBCextMeas hBCextBound
  have hderivBCOn :
      Integrable (fun x ↦ deriv A x * B (C x))
        (volume.restrict (Icc a b)) := by
    refine hderivBCextOn.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hCx := hC hx
    rw [hCext_eq x hx,
      show Bext (C x) = B (C x) by simp [Bext, hCx]]
  have hderivBC :
      IntervalIntegrable (fun x ↦ deriv A x * B (C x)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hderivBCOn

  -- Absolute continuity identifies each stopped derivative integral with
  -- the corresponding endpoint difference, including at either endpoint.
  have hAprimitive (u : ℝ) (hu : u ∈ Icc c d) :
      (∫ x in a..Q u, deriv A x) = A (Q u) - A a := by
    have hQu := hQ hu
    exact (hA.mono (by
      rw [uIcc_of_le hQu.1, uIcc_of_le hab]
      exact Icc_subset_Icc_right hQu.2)).integral_deriv_eq_sub
  have hBprimitive (x : ℝ) (hx : x ∈ Icc a b) :
      (∫ u in C x..d, deriv B u) = B d - B (C x) := by
    have hCx := hC hx
    exact (hB.mono (by
      rw [uIcc_of_le hCx.2, uIcc_of_le hcd]
      exact Icc_subset_Icc_left hCx.1)).integral_deriv_eq_sub

  have hlayer := intervalIntegral_smul_intervalIntegral_of_lt_iff_lt
    (𝕜 := ℝ) (E := ℝ) C Q hab hcd hC hQ hinv
      (deriv B) hBderiv (deriv A) hAderiv
  have hlayer' :
      (∫ u in c..d, deriv B u * (∫ x in a..Q u, deriv A x)) =
        ∫ x in a..b, (∫ u in C x..d, deriv B u) * deriv A x := by
    simpa only [smul_eq_mul] using hlayer
  have hleftPrimitive :
      (∫ u in c..d, deriv B u * (∫ x in a..Q u, deriv A x)) =
        ∫ u in c..d, deriv B u * (A (Q u) - A a) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hcd] at hu
    change deriv B u * (∫ x in a..Q u, deriv A x) =
      deriv B u * (A (Q u) - A a)
    rw [hAprimitive u hu]
  have hrightPrimitive :
      (∫ x in a..b, (∫ u in C x..d, deriv B u) * deriv A x) =
        ∫ x in a..b, (B d - B (C x)) * deriv A x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    change (∫ u in C x..d, deriv B u) * deriv A x =
      (B d - B (C x)) * deriv A x
    rw [hBprimitive x hx]
  have htransport :
      (∫ u in c..d, deriv B u * (A (Q u) - A a)) =
        ∫ x in a..b, (B d - B (C x)) * deriv A x :=
    hleftPrimitive.symm.trans (hlayer'.trans hrightPrimitive)

  -- Both composite products are integrable by the measurable-extension
  -- argument above, so the remaining rearrangement uses genuine linearity
  -- of the Bochner integral rather than totalized-integral simplifications.
  have hAaDerivB :
      IntervalIntegrable (fun u ↦ A a * deriv B u) volume c d :=
    hBderiv.const_mul (A a)
  have hBdDerivA :
      IntervalIntegrable (fun x ↦ B d * deriv A x) volume a b :=
    hAderiv.const_mul (B d)
  have hleftExpand :
      (∫ u in c..d, deriv B u * (A (Q u) - A a)) =
        (∫ u in c..d, A (Q u) * deriv B u) -
          A a * (B d - B c) := by
    calc
      (∫ u in c..d, deriv B u * (A (Q u) - A a)) =
          ∫ u in c..d,
            A (Q u) * deriv B u - A a * deriv B u := by
        apply intervalIntegral.integral_congr
        intro u _hu
        ring
      _ = (∫ u in c..d, A (Q u) * deriv B u) -
          ∫ u in c..d, A a * deriv B u :=
        intervalIntegral.integral_sub hAQderiv hAaDerivB
      _ = (∫ u in c..d, A (Q u) * deriv B u) -
          A a * (B d - B c) := by
        rw [intervalIntegral.integral_const_mul, hB.integral_deriv_eq_sub]
  have hrightExpand :
      (∫ x in a..b, (B d - B (C x)) * deriv A x) =
        B d * (A b - A a) -
          ∫ x in a..b, deriv A x * B (C x) := by
    calc
      (∫ x in a..b, (B d - B (C x)) * deriv A x) =
          ∫ x in a..b,
            B d * deriv A x - deriv A x * B (C x) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        ring
      _ = (∫ x in a..b, B d * deriv A x) -
          ∫ x in a..b, deriv A x * B (C x) :=
        intervalIntegral.integral_sub hBdDerivA hderivBC
      _ = B d * (A b - A a) -
          ∫ x in a..b, deriv A x * B (C x) := by
        rw [intervalIntegral.integral_const_mul, hA.integral_deriv_eq_sub]
  have hrearranged :
      (∫ u in c..d, A (Q u) * deriv B u) -
          A a * (B d - B c) =
        B d * (A b - A a) -
          ∫ x in a..b, deriv A x * B (C x) :=
    hleftExpand.symm.trans (htransport.trans hrightExpand)
  linear_combination hrearranged

/-- **Variable-upper-endpoint inverse-pair identity.**  Under the hypotheses
of `intervalIntegral_deriv_mul_comp_add_comp_mul_deriv_of_lt_iff_lt`, every
`y ∈ [a,b]` cuts out the smaller inverse rectangle
`[a,y] × [c,C y]`.  Consequently,

`∫ₐʸ A'(x) B(C(x)) dx + ∫_c^{C(y)} A(Q(u)) B'(u) du
  = A(y) B(C(y)) - A(a) B(c)`.

The restricted interval-preservation facts are consequences of the same
Galois connection as in the complete identity.  In particular, no new
measurability or differentiability assumption is imposed on either clock. -/
theorem intervalIntegral_deriv_mul_comp_add_comp_mul_deriv_to_of_lt_iff_lt
    (C Q : ℝ → ℝ)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hC : MapsTo C (Icc a b) (Icc c d))
    (hQ : MapsTo Q (Icc c d) (Icc a b))
    (hinv : ∀ ⦃x u : ℝ⦄, x ∈ Icc a b → u ∈ Icc c d →
      (C x < u ↔ x < Q u))
    (A B : ℝ → ℝ)
    (hA : AbsolutelyContinuousOnInterval A a b)
    (hB : AbsolutelyContinuousOnInterval B c d)
    {y : ℝ} (hy : y ∈ Icc a b) :
    (∫ x in a..y, deriv A x * B (C x)) +
      (∫ u in c..C y, A (Q u) * deriv B u) =
        A y * B (C y) - A a * B c := by
  have hCy := hC hy
  have hgc := galoisConnection_Icc_restrict_of_lt_iff_lt C Q hC hQ hinv
  have hCto : MapsTo C (Icc a y) (Icc c (C y)) := by
    intro x hx
    have hx' : x ∈ Icc a b := ⟨hx.1, hx.2.trans hy.2⟩
    refine ⟨(hC hx').1, ?_⟩
    have hxy : (⟨x, hx'⟩ : Icc a b) ≤ ⟨y, hy⟩ := hx.2
    exact hgc.monotone_u hxy
  have hQto : MapsTo Q (Icc c (C y)) (Icc a y) := by
    intro u hu
    have hu' : u ∈ Icc c d := ⟨hu.1, hu.2.trans hCy.2⟩
    refine ⟨(hQ hu').1, ?_⟩
    exact (hgc (⟨u, hu'⟩ : Icc c d) (⟨y, hy⟩ : Icc a b)).mpr hu.2
  have hinvTo : ∀ ⦃x u : ℝ⦄, x ∈ Icc a y → u ∈ Icc c (C y) →
      (C x < u ↔ x < Q u) := by
    intro x u hx hu
    exact hinv ⟨hx.1, hx.2.trans hy.2⟩ ⟨hu.1, hu.2.trans hCy.2⟩
  have hAto : AbsolutelyContinuousOnInterval A a y :=
    hA.mono (by
      rw [uIcc_of_le hy.1, uIcc_of_le hab]
      exact Icc_subset_Icc_right hy.2)
  have hBto : AbsolutelyContinuousOnInterval B c (C y) :=
    hB.mono (by
      rw [uIcc_of_le hCy.1, uIcc_of_le hcd]
      exact Icc_subset_Icc_right hCy.2)
  exact intervalIntegral_deriv_mul_comp_add_comp_mul_deriv_of_lt_iff_lt
    C Q hy.1 hCy.1 hCto hQto hinvTo A B hAto hBto

/-- **Absolutely-continuous inverse-pair identity for the Fabius clocks.**
For absolutely continuous `A` and `B` on the unit interval, the two terms
obtained by composing through `fabiusReal` and `fabiusInv` add to the endpoint
product difference.  No differentiability of either Fabius clock is used. -/
theorem intervalIntegral_deriv_mul_fabiusReal_add_fabiusInv_mul_deriv
    (F : BoundedFabius) (hF : IsFabius F)
    (A B : ℝ → ℝ)
    (hA : AbsolutelyContinuousOnInterval A 0 1)
    (hB : AbsolutelyContinuousOnInterval B 0 1) :
    (∫ x in (0 : ℝ)..1, deriv A x * B (fabiusReal F x)) +
      (∫ u in (0 : ℝ)..1, A (fabiusInv F hF u) * deriv B u) =
        A 1 * B 1 - A 0 * B 0 := by
  apply intervalIntegral_deriv_mul_comp_add_comp_mul_deriv_of_lt_iff_lt
    (C := fabiusReal F) (Q := fabiusInv F hF)
  · norm_num
  · norm_num
  · intro x _hx
    exact ⟨fabiusReal_nonneg F x, fabiusReal_le_one F x⟩
  · intro u _hu
    exact fabiusInv_mem_Icc F hF u
  · intro x u hx hu
    exact fabiusReal_lt_iff_lt_fabiusInv F hF hx hu
  · exact hA
  · exact hB

/-- **Variable-upper-endpoint Fabius inverse-pair identity.**  For every
`y ∈ [0,1]`, the complete proper-compact identity restricts to the inverse
rectangle `[0,y] × [0,fabiusReal F y]`. -/
theorem intervalIntegral_deriv_mul_fabiusReal_add_fabiusInv_mul_deriv_to
    (F : BoundedFabius) (hF : IsFabius F)
    (A B : ℝ → ℝ)
    (hA : AbsolutelyContinuousOnInterval A 0 1)
    (hB : AbsolutelyContinuousOnInterval B 0 1)
    {y : ℝ} (hy : y ∈ Icc 0 1) :
    (∫ x in (0 : ℝ)..y, deriv A x * B (fabiusReal F x)) +
      (∫ u in (0 : ℝ)..fabiusReal F y,
        A (fabiusInv F hF u) * deriv B u) =
        A y * B (fabiusReal F y) - A 0 * B 0 := by
  apply intervalIntegral_deriv_mul_comp_add_comp_mul_deriv_to_of_lt_iff_lt
    (C := fabiusReal F) (Q := fabiusInv F hF)
    (a := 0) (b := 1) (c := 0) (d := 1)
  · norm_num
  · norm_num
  · intro x _hx
    exact ⟨fabiusReal_nonneg F x, fabiusReal_le_one F x⟩
  · intro u _hu
    exact fabiusInv_mem_Icc F hF u
  · intro x u hx hu
    exact fabiusReal_lt_iff_lt_fabiusInv F hF hx hu
  · exact hA
  · exact hB
  · exact hy

/-- The classical inverse-graph area identity for the Fabius inverse pair:
the areas below `fabiusReal` and `fabiusInv` on the unit interval add to the
area of the unit square. -/
theorem intervalIntegral_fabiusReal_add_fabiusInv_eq_one
    (F : BoundedFabius) (hF : IsFabius F) :
    (∫ x in (0 : ℝ)..1, fabiusReal F x) +
      (∫ u in (0 : ℝ)..1, fabiusInv F hF u) = 1 := by
  have hid : AbsolutelyContinuousOnInterval (id : ℝ → ℝ) 0 1 :=
    (contDiffOn_id :
      ContDiffOn ℝ 1 (id : ℝ → ℝ) (uIcc (0 : ℝ) 1)).absolutelyContinuousOnInterval
  simpa only [deriv_id', id_eq, one_mul, mul_one, zero_mul, sub_zero] using
    (intervalIntegral_deriv_mul_fabiusReal_add_fabiusInv_mul_deriv
      F hF id id hid hid)

/-- **Partial inverse-area identity for the Fabius inverse.**  For
`u ∈ [0,1]`, the area below the inverse graph up to `u` is the area of the
rectangle with sides `u` and `fabiusInv F hF u`, minus the area below
`fabiusReal F` up to the inverse endpoint. -/
theorem intervalIntegral_fabiusInv_to_eq_mul_sub_intervalIntegral_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F)
    {u : ℝ} (hu : u ∈ Icc 0 1) :
    (∫ v in (0 : ℝ)..u, fabiusInv F hF v) =
      u * fabiusInv F hF u -
        ∫ x in (0 : ℝ)..fabiusInv F hF u, fabiusReal F x := by
  have hid : AbsolutelyContinuousOnInterval (id : ℝ → ℝ) 0 1 :=
    (contDiffOn_id :
      ContDiffOn ℝ 1 (id : ℝ → ℝ) (uIcc (0 : ℝ) 1)).absolutelyContinuousOnInterval
  have harea :=
    intervalIntegral_deriv_mul_fabiusReal_add_fabiusInv_mul_deriv_to
      F hF id id hid hid (fabiusInv_mem_Icc F hF u)
  apply (eq_sub_iff_add_eq).2
  simpa only [deriv_id', id_eq, one_mul, mul_one, zero_mul, sub_zero,
    fabiusReal_fabiusInv F hF hu, add_comm, mul_comm] using harea

end Fabius
