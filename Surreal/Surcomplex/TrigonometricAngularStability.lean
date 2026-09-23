import Surreal.Surcomplex.TrigonometricCayleyStability
import Surreal.Surcomplex.CayleyAngularBounds

/-!
# Angular displacement bounds for actual trigonometric polynomials

The rational-chart root becomes an actual infinitesimal angular displacement.
Existence, uniqueness on the full angular valuation neighborhood and both
bounds in `trigonometry:thm:stability` are proved here, together with a simple
numerator certificate. `TrigonometricPolynomialDerivative` identifies the
Fourier derivative with the fine derivative and proves angular simplicity.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Evaluation in the inverse Cayley chart is evaluation at the actual shifted angle. -/
theorem trigonometricCayley_inverse (p : LaurentPolynomial Surcomplex.{u})
    (a : SignSequence.FiniteElement.{u}) (x : SignSequence.{u}) :
    trigonometricCayley p a x =
      (trigonometricPolynomial p (a + angularCayleyInverse x)).re := by
  unfold trigonometricCayley trigonometricPolynomial
  congr 2
  apply Units.ext
  simp only [Units.val_mul, Unitary.val_toUnits_apply, phaseUnit_val]
  rw [finitePhase_add, finitePhase_angularCayleyInverse]

/-- Every infinitesimal shifted angle is represented in the exact rational chart. -/
theorem trigonometricCayley_coordinate (p : LaurentPolynomial Surcomplex.{u})
    (a h : SignSequence.FiniteElement.{u}) (hh : SignSequence.IsInfinitesimal h.val) :
    trigonometricCayley p a (angularCayleyCoordinate h) =
      (trigonometricPolynomial p (a + h)).re := by
  rw [trigonometricCayley_inverse, angularCayleyInverse_coordinate h hh]

/-- Angular root existence, full-neighborhood uniqueness and both valuation bounds,
with the coefficient-defined Fourier derivative. -/
theorem trigonometric_angular_root_bounds
    (p g : LaurentPolynomial Surcomplex.{u}) (a : SignSequence.FiniteElement.{u})
    (k s : SignSequence.{u})
    (hp : ∀ n ∈ p.coeff.support, IsFinite (p.coeff n))
    (hg : ∀ n ∈ g.coeff.support, (s : WithTop SignSequence.{u}) ≤ valuation (g.coeff n))
    (ha : (trigonometricPolynomial p a).re = 0)
    (hA : SignSequence.valuation (trigonometricFourierDerivative p a) = ↑k)
    (hk : 0 ≤ k) (hs : 2 * k < s) :
    ∃ h : SignSequence.FiniteElement.{u},
      (k : WithTop SignSequence.{u}) < SignSequence.valuation h.val ∧
      (trigonometricPolynomial (p + g) (a + h)).re = 0 ∧
      (∃ N : ℕ, (∀ n ∈ (p + g).coeff.support, n.natAbs ≤ N) ∧
        (trigonometricNumerator (p + g) a N).rootMultiplicity (angularCayleyCoordinate h) = 1) ∧
      (s - k : SignSequence.{u}) ≤ SignSequence.valuation h.val ∧
      (2 * s - 3 * k : SignSequence.{u}) ≤ SignSequence.valuation
        (h.val + (trigonometricPolynomial g a).re / trigonometricFourierDerivative p a) ∧
      ∀ h' : SignSequence.FiniteElement.{u},
        (k : WithTop SignSequence.{u}) < SignSequence.valuation h'.val →
        (trigonometricPolynomial (p + g) (a + h')).re = 0 → h' = h := by
  obtain ⟨Np, hNp⟩ := LaurentCayley.exists_frequency_bound p
  obtain ⟨Ng, hNg⟩ := LaurentCayley.exists_frequency_bound g
  let N := max Np Ng
  have hNp' : ∀ n ∈ p.coeff.support, n.natAbs ≤ N :=
    fun n hn => (hNp n hn).trans (le_max_left _ _)
  have hNg' : ∀ n ∈ g.coeff.support, n.natAbs ≤ N :=
    fun n hn => (hNg n hn).trans (le_max_right _ _)
  obtain ⟨x, hx, hz, hm, hb, he, hu⟩ := trigonometric_cayley_root_stability
    p g a N k s hNp' hNg' hp hg ha hA hk hs
  have hki : (0 : WithTop SignSequence.{u}) ≤ ↑k := WithTop.coe_nonneg.mpr hk
  have hxi : SignSequence.IsInfinitesimal x :=
    (SignSequence.isInfinitesimal_iff_valuation_pos _).mpr (hki.trans_lt hx)
  have hv := valuation_angularCayleyInverse x hxi
  refine ⟨angularCayleyInverse x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [hv]
  · rwa [trigonometricCayley_inverse] at hz
  · exact ⟨N, trigonometric_frequency_bound_add p g N hNp' hNg',
      by simpa only [angularCayleyCoordinate_inverse] using hm⟩
  · rwa [hv]
  · exact angularCayleyInverse_correction_bound x
      ((trigonometricPolynomial g a).re / trigonometricFourierDerivative p a) k s hk hs hb he
  · intro h' hh' hr
    have hi : SignSequence.IsInfinitesimal h'.val :=
      (SignSequence.isInfinitesimal_iff_valuation_pos _).mpr (hki.trans_lt hh')
    have hv' := valuation_angularCayleyCoordinate h' hi
    have hc := hu (angularCayleyCoordinate h') (hv' ▸ hh')
      (by rwa [trigonometricCayley_coordinate (p + g) a h' hi])
    rw [← angularCayleyInverse_coordinate h' hi, hc]

end
end Surreal.Surcomplex
