import Surreal.Foundations.SmallNormalFormLeading
import Surreal.Foundations.SignSequenceRealBirthday

/-!
# Real constants in the canonical cut evaluation

The candidate for a single formal term is a sign prefix of the corresponding
actual monomial. At exponent zero this prefix is the real number itself:
a proper prefix of a real has finite birthday and is dyadic, so equality of
leading coefficients rules out a proper prefix. This establishes exact
evaluation of real constants without assuming uniqueness from valuation
approximation or evaluation of arbitrary monomials.
-/

universe u

namespace Surreal.Foundations

noncomputable section

namespace SignSequence

/-- A sign prefix of a real with the same leading coefficient is that real.
The finite-birthday characterization of dyadics supplies the needed rigidity. -/
theorem eq_of_isPrefix_ofReal_of_leadingCoeff (x : SignSequence.{u}) (r : ℝ)
    (hp : IsPrefix x (ofReal r)) (hc : leadingCoeff x = r) : x = ofReal r := by
  by_contra hne
  have hbirth : x.birthday < (ofReal r : SignSequence.{u}).birthday := by
    apply lt_of_le_of_ne hp.1
    intro h
    apply hne
    apply hp.antisymm
    exact ⟨h.ge, fun i hi => (hp.2 i (by simpa only [h] using hi)).symm⟩
  have hxω := hbirth.trans_le (birthday_ofReal_le_omega0 r)
  obtain ⟨q, hq⟩ := (birthday_lt_omega0_iff_dyadic x).mp hxω
  have heq : x = ofReal (q.toRat : ℝ) := by
    simpa only [ofReal_ratCast] using hq.symm
  rw [heq, leadingCoeff_ofReal] at hc
  exact hne (heq.trans (congrArg ofReal hc))

end SignSequence

namespace SmallNormalForm

open SignSequence

/-- Truncation strictly above the only possible exponent of a singleton is empty. -/
@[simp] theorem trunc_single_self (a : SignSequence.{u}) (r : ℝ) :
    trunc (single a r) a = 0 := by
  apply ext
  intro b
  simp only [coeff_trunc, coeff_single, coeff_zero]
  by_cases h : b = a
  · simp [h]
  · simp [h]

/-- The actual monomial satisfies the singleton candidate's defining bound,
so the canonical candidate is a sign prefix of it. -/
theorem cutEvaluation_single_isPrefix (a : SignSequence.{u}) (r : ℝ) :
    IsPrefix (cutEvaluation (single a r)) (ofReal r * omegaPower a) := by
  apply cutEvaluation_isPrefix
  intro b hb
  have hba : b = a := by
    by_contra h
    simp only [mem_support, coeff_single, if_neg h, ne_eq, not_true_eq_false] at hb
  subst b
  simp [trunc_single_self]
  exact WithTop.coe_lt_top (a := (-a : SignSequence.{u}))

/-- The canonical cut evaluation agrees with the actual embedding of every
ordinary real constant, including zero. -/
@[simp] theorem cutEvaluation_single_zero (r : ℝ) :
    cutEvaluation (single (0 : SignSequence.{u}) r) = ofReal r := by
  by_cases hr : r = 0
  · subst r
    have hf : single (0 : SignSequence.{u}) 0 = 0 := by
      apply ext
      intro a
      simp
    rw [hf, cutEvaluation_zero, map_zero]
  apply eq_of_isPrefix_ofReal_of_leadingCoeff
  · simpa only [omegaPower_zero, _root_.mul_one] using
      cutEvaluation_single_isPrefix (0 : SignSequence.{u}) r
  · have ha : (0 : SignSequence.{u}) ∈ support (single 0 r) := by simpa using hr
    have h := cutEvaluation_remainder (single (0 : SignSequence.{u}) r) 0 ha
    simp [trunc_single_self] at h
    have hl := leading_of_valuation_sub_gt
      (cutEvaluation (single (0 : SignSequence.{u}) r)) 0 r hr
      (by simpa only [tMonomial, neg_zero, omegaPower_zero, _root_.mul_one,
        WithTop.coe_zero] using h)
    exact hl.2

end SmallNormalForm

end

end Surreal.Foundations
