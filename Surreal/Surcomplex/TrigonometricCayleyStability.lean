import Surreal.Surcomplex.TrigonometricPolynomialCayley
import Surreal.Foundations.SignSequencePolynomialStabilityError

/-!
# Root stability for actual trigonometric polynomials in Cayley coordinates

This proves the exact rational-chart step of `trigonometry:thm:stability`,
including existence, uniqueness throughout the prescribed open valuation
neighborhood, simple polynomial multiplicity and both error bounds. The
variable here is `x = 2 tan(h/2)`; transferring the bounds and simplicity to
the angle `h`, and identifying the Fourier derivative with the fine
derivative, are subsequent obligations.
-/

universe u

namespace Surreal.Surcomplex

open Foundations Polynomial

noncomputable section

/-- The two sharp stability bounds hold for the exact Cayley pullback of a
finite Laurent polynomial, at arbitrary surreal valuation ranks. -/
theorem trigonometric_cayley_root_stability
    (p g : LaurentPolynomial Surcomplex.{u}) (a : SignSequence.FiniteElement.{u})
    (N : ℕ) (k s : SignSequence.{u})
    (hNp : ∀ n ∈ p.coeff.support, n.natAbs ≤ N)
    (hNg : ∀ n ∈ g.coeff.support, n.natAbs ≤ N)
    (hp : ∀ n ∈ p.coeff.support, IsFinite (p.coeff n))
    (hg : ∀ n ∈ g.coeff.support, (s : WithTop SignSequence.{u}) ≤ valuation (g.coeff n))
    (ha : (trigonometricPolynomial p a).re = 0)
    (hA : SignSequence.valuation (trigonometricFourierDerivative p a) = ↑k)
    (hk : 0 ≤ k) (hs : 2 * k < s) :
    ∃ x : SignSequence.{u},
      (k : WithTop SignSequence.{u}) < SignSequence.valuation x ∧
      trigonometricCayley (p + g) a x = 0 ∧
      (trigonometricNumerator (p + g) a N).rootMultiplicity x = 1 ∧
      (s - k : SignSequence.{u}) ≤ SignSequence.valuation x ∧
      (2 * s - 3 * k : SignSequence.{u}) ≤ SignSequence.valuation
        (x + (trigonometricPolynomial g a).re / trigonometricFourierDerivative p a) ∧
      ∀ y, (k : WithTop SignSequence.{u}) < SignSequence.valuation y →
        trigonometricCayley (p + g) a y = 0 → y = x := by
  have hs0 : 0 ≤ s := by linarith
  have hgf : ∀ n ∈ g.coeff.support, IsFinite (g.coeff n) := by
    intro n hn
    apply (isFinite_iff_valuation_nonneg _).mpr
    exact (show (0 : WithTop SignSequence.{u}) ≤ ↑s from
      WithTop.coe_nonneg.mpr hs0).trans (hg n hn)
  have h0 : (trigonometricNumerator (p + g) a N).coeff 0 =
      (trigonometricPolynomial g a).re := by
    rw [trigonometricNumerator_add, coeff_add, trigonometricNumerator_coeff_zero,
      trigonometricNumerator_coeff_zero, ha, zero_add]
  have h1 : (trigonometricNumerator (p + g) a N).coeff 1 -
      trigonometricFourierDerivative p a = (trigonometricNumerator g a N).coeff 1 := by
    rw [trigonometricNumerator_add, coeff_add, trigonometricNumerator_coeff_one p a N hNp]
    ring
  have hb0 : (s : WithTop SignSequence.{u}) ≤
      SignSequence.valuation ((trigonometricNumerator (p + g) a N).coeff 0) := by
    rw [h0, ← trigonometricNumerator_coeff_zero g a N]
    exact trigonometricNumerator_valuation g a N s hg 0
  have hb1 : (s : WithTop SignSequence.{u}) ≤ SignSequence.valuation
      ((trigonometricNumerator (p + g) a N).coeff 1 - trigonometricFourierDerivative p a) := by
    rw [h1]
    exact trigonometricNumerator_valuation g a N s hg 1
  have hh : ∀ n, SignSequence.IsFinite
      ((trigonometricNumerator (p + g) a N).coeff (n + 2)) := by
    intro n
    rw [trigonometricNumerator_add, coeff_add]
    exact SignSequence.finite_add (trigonometricNumerator_finite p a N hp _)
      (trigonometricNumerator_finite g a N hgf _)
  obtain ⟨x, hx, hr, hm, hb, he, hu⟩ := SignSequence.polynomial_root_stability
    (trigonometricNumerator (p + g) a N) (trigonometricFourierDerivative p a) k s
    hA hk hs hb0 hb1 hh
  have hN := trigonometric_frequency_bound_add p g N hNp hNg
  refine ⟨x, hx, (isRoot_trigonometricNumerator_iff (p + g) a N hN x).mp hr,
    hm, hb, ?_, ?_⟩
  · rwa [h0] at he
  · intro y hy hroot
    exact hu y hy ((isRoot_trigonometricNumerator_iff (p + g) a N hN y).mpr hroot)

end
end Surreal.Surcomplex
