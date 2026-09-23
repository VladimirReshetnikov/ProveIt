import Surreal.Surcomplex.SineSquareExpansion

/-!
# Exact error valuations and the threshold counterexample for sine square

These are the valuation calculations in `trigonometry:prop:sharp`. A
smaller angular displacement gives a constant perturbation attaining both
stability bounds. At the threshold, cancelling the constant term leaves
no zero in the original open angular neighborhood.
-/

universe u

namespace Surreal.Surcomplex.SineSquare

open Foundations

noncomputable section

/-- The constant perturbation that makes the displaced angle a root. -/
def perturbation (a h : SignSequence.FiniteElement.{u}) : SignSequence.{u} :=
  finiteSin a ^ 2 - finiteSin (a + h) ^ 2

/-- The shifted angle is an exact root after adding this constant. -/
theorem perturbed_root (a h : SignSequence.FiniteElement.{u}) :
    function (finiteSin a ^ 2) (a + h).val + perturbation a h = 0 := by
  rw [function_eval, perturbation]
  ring

/-- Both error exponents are attained for every pair of distinct positive infinitesimal scales. -/
theorem exact_error_valuations (a h : SignSequence.FiniteElement.{u})
    (ha : SignSequence.IsInfinitesimal a.val) (hh : SignSequence.IsInfinitesimal h.val)
    (k r : SignSequence.{u}) (hva : SignSequence.valuation a.val = ↑k)
    (hvh : SignSequence.valuation h.val = ↑r) (hkr : k < r) :
    SignSequence.valuation (perturbation a h) = ↑(k + r) ∧
      SignSequence.valuation (h.val + perturbation a h / slope a) = ↑(2 * r - k) := by
  obtain ⟨Q, hQ, hstd, he⟩ := quadratic_remainder a h ha hh
  have hQv : SignSequence.valuation Q = 0 :=
    (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero hQ).mpr
      (by rw [hstd]; exact one_ne_zero)
  have hAv : SignSequence.valuation (slope a) = ↑k := (valuation_slope a ha).trans hva
  have hA0 : slope a ≠ 0 := by
    intro hz
    rw [hz, SignSequence.valuation_zero] at hAv
    exact WithTop.top_ne_coe hAv
  have hlin : SignSequence.valuation (slope a * h.val) = ↑(k + r) := by
    rw [SignSequence.valuation_mul, hAv, hvh, WithTop.coe_add]
  have hquad : SignSequence.valuation (h.val ^ 2 * Q) = ↑(r + r) := by
    rw [pow_two, SignSequence.valuation_mul, SignSequence.valuation_mul,
      hvh, hQv, add_zero, WithTop.coe_add]
  have hd : perturbation a h = -(slope a * h.val + h.val ^ 2 * Q) := by
    rw [perturbation, he]
    ring
  constructor
  · rw [hd, SignSequence.valuation_neg,
      SignSequence.valuation.map_add_eq_of_lt_left (by
        rw [hlin, hquad, WithTop.coe_lt_coe]
        linarith), hlin]
  · have hc : h.val + perturbation a h / slope a = -(h.val ^ 2 * Q / slope a) := by
      rw [hd]
      field_simp
      ring
    rw [hc, SignSequence.valuation_neg, SignSequence.valuation_div, hquad, hAv]
    change ((r + r - k : SignSequence.{u}) : WithTop SignSequence.{u}) = ↑(2 * r - k)
    congr 1
    ring

/-- At the equality threshold, cancelling the constant term loses the root
throughout the original neighborhood, not just its simplicity. -/
theorem threshold_no_root (a : SignSequence.FiniteElement.{u})
    (ha : SignSequence.IsInfinitesimal a.val) (k : SignSequence.{u})
    (hva : SignSequence.valuation a.val = ↑k) (hk : 0 ≤ k)
    (y : SignSequence.{u}) (hy : (k : WithTop SignSequence.{u}) < SignSequence.valuation y) :
    function (finiteSin a ^ 2) (a.val + y) + finiteSin a ^ 2 ≠ 0 := by
  have hyi : SignSequence.IsInfinitesimal y :=
    (SignSequence.isInfinitesimal_iff_valuation_pos _).mpr
      ((show (0 : WithTop SignSequence.{u}) ≤ ↑k from WithTop.coe_nonneg.mpr hk).trans_lt hy)
  let z : SignSequence.FiniteElement.{u} :=
    ⟨a.val + y, SignSequence.finite_add a.property (SignSequence.finite_of_infinitesimal hyi)⟩
  have hzi : SignSequence.IsInfinitesimal z.val := SignSequence.infinitesimal_add ha hyi
  have hzv : SignSequence.valuation z.val = ↑k := by
    change SignSequence.valuation (a.val + y) = _
    rw [SignSequence.valuation.map_add_eq_of_lt_left (hva ▸ hy), hva]
  have hsv : SignSequence.valuation (finiteSin z) = ↑k :=
    (valuation_finiteSin_of_isInfinitesimal z hzi).trans hzv
  have hsn : finiteSin z ≠ 0 := by
    intro hz
    rw [hz, SignSequence.valuation_zero] at hsv
    exact WithTop.top_ne_coe hsv
  change function (finiteSin a ^ 2) z.val + finiteSin a ^ 2 ≠ 0
  rw [function_eval, sub_add_cancel]
  exact pow_ne_zero _ hsn

/-- The cancelling constant has exactly twice the original derivative valuation. -/
theorem threshold_valuation (a : SignSequence.FiniteElement.{u})
    (ha : SignSequence.IsInfinitesimal a.val) (k : SignSequence.{u})
    (hva : SignSequence.valuation a.val = ↑k) :
    SignSequence.valuation (finiteSin a ^ 2) = ↑(2 * k) := by
  rw [pow_two, SignSequence.valuation_mul, valuation_finiteSin_of_isInfinitesimal a ha, hva,
    ← WithTop.coe_add, ← two_mul]

end
end Surreal.Surcomplex.SineSquare
