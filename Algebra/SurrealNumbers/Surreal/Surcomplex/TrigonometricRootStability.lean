import Surreal.Surcomplex.TrigonometricPolynomialDerivative

/-!
# Sharp angular root stability in the actual surreal field

This completes `trigonometry:thm:stability`, `trigonometry:eq:stabilitythreshold`,
`trigonometry:eq:stabilityfirst` and `trigonometry:eq:stabilitysecond`.
The derivative hypothesis and simplicity conclusion use native fine derivatives;
uniqueness ranges over every actual surreal displacement in the indicated
valuation neighborhood. The separate sharpness proposition is proved in
`TrigonometricStabilitySharpness`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- A finite real trigonometric polynomial retains one simple angular root
under a perturbation with coefficient valuation `σ > 2κ`, with both bounds.
The functions are real parts of arbitrary Mathlib surcomplex Laurent polynomials;
in particular this includes every real-valued Laurent presentation. -/
theorem trigonometric_root_stability
    (p g : LaurentPolynomial Surcomplex.{u}) (a : SignSequence.FiniteElement.{u})
    (A k s : SignSequence.{u})
    (hp : ∀ n ∈ p.coeff.support, IsFinite (p.coeff n))
    (hg : ∀ n ∈ g.coeff.support, (s : WithTop SignSequence.{u}) ≤ valuation (g.coeff n))
    (ha : trigonometricFunction p a.val = 0)
    (hder : FineHasDerivAt (trigonometricFunction p) A a.val)
    (hA : SignSequence.valuation A = ↑k) (hk : 0 ≤ k) (hs : 2 * k < s) :
    ∃ h : SignSequence.{u},
      (k : WithTop SignSequence.{u}) < SignSequence.valuation h ∧
      trigonometricFunction (p + g) (a.val + h) = 0 ∧
      (∃ D : SignSequence.{u}, D ≠ 0 ∧
        FineHasDerivAt (trigonometricFunction (p + g)) D (a.val + h)) ∧
      (s - k : SignSequence.{u}) ≤ SignSequence.valuation h ∧
      (2 * s - 3 * k : SignSequence.{u}) ≤
        SignSequence.valuation (h + trigonometricFunction g a.val / A) ∧
      ∀ y : SignSequence.{u}, (k : WithTop SignSequence.{u}) < SignSequence.valuation y →
        trigonometricFunction (p + g) (a.val + y) = 0 → y = h := by
  have hAid : A = trigonometricFourierDerivative p a :=
    hder.unique (fineHasDerivAt_trigonometricFunction p a)
  have hAf : SignSequence.valuation (trigonometricFourierDerivative p a) = ↑k := hAid ▸ hA
  have haf : (trigonometricPolynomial p a).re = 0 := by
    rwa [trigonometricFunction_eq] at ha
  obtain ⟨h, hv, hz, ⟨N, hN, hm⟩, hb, he, hu⟩ :=
    trigonometric_angular_root_bounds p g a k s hp hg haf hAf hk hs
  have hki : (0 : WithTop SignSequence.{u}) ≤ ↑k := WithTop.coe_nonneg.mpr hk
  have hi : SignSequence.IsInfinitesimal h.val :=
    (SignSequence.isInfinitesimal_iff_valuation_pos _).mpr (hki.trans_lt hv)
  have hr : (trigonometricNumerator (p + g) a N).IsRoot (angularCayleyCoordinate h) := by
    rw [isRoot_trigonometricNumerator_iff (p + g) a N hN,
      trigonometricCayley_coordinate (p + g) a h hi]
    exact hz
  have hsimple := trigonometricFourierDerivative_ne_zero_of_simple_numerator
    (p + g) a N hN (angularCayleyCoordinate h) hr hm
  rw [angularCayleyInverse_coordinate h hi] at hsimple
  refine ⟨h.val, hv, ?_, ?_, hb, ?_, ?_⟩
  · change trigonometricFunction (p + g) (a + h).val = 0
    rwa [trigonometricFunction_eq]
  · exact ⟨trigonometricFourierDerivative (p + g) (a + h), hsimple,
      fineHasDerivAt_trigonometricFunction (p + g) (a + h)⟩
  · rwa [trigonometricFunction_eq, hAid]
  · intro y hy hyr
    have hyi : SignSequence.IsInfinitesimal y :=
      (SignSequence.isInfinitesimal_iff_valuation_pos _).mpr (hki.trans_lt hy)
    let y' : SignSequence.FiniteElement.{u} := ⟨y, SignSequence.finite_of_infinitesimal hyi⟩
    have hyr' : (trigonometricPolynomial (p + g) (a + y')).re = 0 := by
      change trigonometricFunction (p + g) (a + y').val = 0 at hyr
      rwa [trigonometricFunction_eq] at hyr
    exact congrArg (fun z : SignSequence.FiniteElement.{u} => z.val) (hu y' hy hyr')

end
end Surreal.Surcomplex
