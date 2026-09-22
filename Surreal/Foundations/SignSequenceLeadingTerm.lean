import Surreal.Foundations.SignSequenceFiniteLeading

/-!
# Leading-term removal and monomial approximation in the actual sign field

Removing the actual leading monomial strictly raises valuation. Conversely,
approximation by a nonzero real monomial to strictly higher valuation fixes
both its exponent and coefficient. These are the local extraction steps for
the infinite normal-form theorem; no termination or complete expansion is
asserted here.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The genuine first monomial term of an actual surreal. -/
def leadingTerm (x : SignSequence.{u}) : SignSequence.{u} :=
  ofReal (leadingCoeff x) * omegaPower (leadingExponent x)

@[simp] theorem toSurreal_leadingTerm (x : SignSequence.{u}) :
    toSurreal (leadingTerm x) = _root_.Surreal.leadingTerm (toSurreal x) := by
  simp only [leadingTerm, toSurreal_mul, toSurreal_ofReal, toSurreal_omegaPower,
    toSurreal_leadingExponent, leadingCoeff, _root_.Surreal.leadingTerm]

@[simp] theorem leadingTerm_zero : leadingTerm (0 : SignSequence.{u}) = 0 := by
  simp [leadingTerm]

@[simp] theorem leadingTerm_eq_zero_iff (x : SignSequence.{u}) :
    leadingTerm x = 0 ↔ x = 0 := by
  simp [leadingTerm, omegaPower_ne_zero]

/-- Removing the leading term gives an error of strictly greater valuation. -/
theorem valuation_lt_sub_leadingTerm {x : SignSequence.{u}} (hx : x ≠ 0) :
    valuation x < valuation (x - leadingTerm x) := by
  apply (valuation_lt_iff _ _).mpr
  apply (archimedeanClass_toSurreal_lt_iff _ _).mp
  have hx' : toSurreal x ≠ 0 := by
    intro hz
    exact hx ((toSurreal_inj x 0).mp (hz.trans toSurreal_zero.symm))
  simpa only [toSurreal_sub, toSurreal_leadingTerm] using
    _root_.Surreal.mk_lt_mk_sub_leadingTerm hx'

@[simp] theorem valuation_leadingTerm (x : SignSequence.{u}) :
    valuation (leadingTerm x) = valuation x := by
  apply (valuation_eq_iff _ _).mpr
  apply (archimedeanClass_toSurreal_eq_iff _ _).mp
  simpa only [toSurreal_leadingTerm] using _root_.Surreal.mk_leadingTerm (toSurreal x)

@[simp] theorem leadingCoeff_leadingTerm (x : SignSequence.{u}) :
    leadingCoeff (leadingTerm x) = leadingCoeff x := by
  simp only [leadingTerm, leadingCoeff_mul, leadingCoeff_ofReal,
    leadingCoeff_omegaPower, mul_one]

@[simp] theorem leadingExponent_leadingTerm (x : SignSequence.{u}) :
    leadingExponent (leadingTerm x) = leadingExponent x := by
  apply (toSurreal_inj _ _).mp
  simp only [toSurreal_leadingExponent, toSurreal_leadingTerm, _root_.Surreal.wlog_leadingTerm]

@[simp] theorem leadingTerm_leadingTerm (x : SignSequence.{u}) :
    leadingTerm (leadingTerm x) = leadingTerm x := by
  change ofReal (leadingCoeff (leadingTerm x)) * omegaPower (leadingExponent (leadingTerm x)) = _
  rw [leadingCoeff_leadingTerm, leadingExponent_leadingTerm]
  rfl

/-- A higher-valuation error cannot change either datum of a specified
nonzero monomial in the increasing-exponent convention. -/
theorem leading_of_valuation_sub_gt (x a : SignSequence.{u}) (r : ℝ) (hr : r ≠ 0)
    (h : (a : WithTop SignSequence.{u}) < valuation (x - ofReal r * tMonomial a)) :
    valuation x = (a : WithTop SignSequence.{u}) ∧ leadingCoeff x = r := by
  let m := ofReal r * tMonomial a
  have hm : valuation m = (a : WithTop SignSequence.{u}) := valuation_real_mul_tMonomial hr a
  have hv : valuation m < valuation (x - m) := by rw [hm]; exact h
  have hsum : m + (x - m) = x := by abel
  constructor
  · have he := valuation.map_add_of_distinct_val hv.ne
    rw [hsum, min_eq_left hv.le, hm] at he
    exact he
  · have he := leadingCoeff_add_of_valuation_lt hv
    simpa only [hsum, m, leadingCoeff_real_mul_tMonomial] using he

/-- The same extraction statement for decreasing Conway growth exponents. -/
theorem leading_of_valuation_sub_omega_gt (x a : SignSequence.{u}) (r : ℝ) (hr : r ≠ 0)
    (h : ((-a : SignSequence.{u}) : WithTop SignSequence.{u}) <
      valuation (x - ofReal r * omegaPower a)) :
    leadingExponent x = a ∧ leadingCoeff x = r := by
  have hlead := leading_of_valuation_sub_gt x (-a) r hr (by simpa only [tMonomial, neg_neg] using h)
  have hx : x ≠ 0 := (leadingCoeff_eq_zero_iff x).not.mp (by rw [hlead.2]; exact hr)
  refine ⟨?_, hlead.2⟩
  apply neg_injective
  exact WithTop.coe_injective ((valuation_of_ne_zero hx).symm.trans hlead.1)

/-- Agreement with a nonzero leading monomial is equivalent to the exact
exponent and coefficient data, with a strict error bound. -/
theorem valuation_sub_omega_gt_iff (x a : SignSequence.{u}) (r : ℝ) (hr : r ≠ 0) :
    ((-a : SignSequence.{u}) : WithTop SignSequence.{u}) <
        valuation (x - ofReal r * omegaPower a) ↔
      leadingExponent x = a ∧ leadingCoeff x = r := by
  constructor
  · exact leading_of_valuation_sub_omega_gt x a r hr
  · intro h
    have hx : x ≠ 0 := (leadingCoeff_eq_zero_iff x).not.mp (by rw [h.2]; exact hr)
    simpa only [valuation_of_ne_zero hx, leadingTerm, h.1, h.2] using
      valuation_lt_sub_leadingTerm hx

end

end Surreal.Foundations.SignSequence
