import Surreal.Algebra.FormalExponentialCoordinate
import Surreal.Algebra.LaurentCoordinateMultiplicity
import Surreal.Surcomplex.InfinitesimalPhase
import Surreal.Surcomplex.TrigonometricPolynomialRootCount

/-!
# Formal angular germs of actual Laurent polynomials

The unit coordinate `z exp(iH)` has constant coefficient `z` and nonzero
linear coefficient `iz`. Substitution of a finite Laurent sum therefore
preserves native polynomial multiplicities (`trigonometry:thm:polyroots`).
The frequency decomposition exposes ordinary exponential series with actual
surcomplex scalar factors, for the strong evaluation bridge.
-/

universe u
namespace Surreal.Surcomplex.AngularLaurent

open Foundations FormalExponentialCoordinate

noncomputable section

/-- The actual coefficient embedding preserves scalar formal exponential series. -/
theorem map_series (a : ℂ) :
    PowerSeries.map ofComplex (series a) = series (ofComplex a : Surcomplex.{u}) := by
  rw [series, ← PowerSeries.rescale_map, PowerSeries.map_exp]
  rfl

/-- The local exponential coordinate, bundled as a formal unit. -/
def coordinate (z : Surcomplex.{u}ˣ) : (PowerSeries Surcomplex.{u})ˣ :=
  Units.map PowerSeries.C.toMonoidHom z * exponentialUnit I

@[simp] theorem coordinate_val (z : Surcomplex.{u}ˣ) :
    (coordinate z).val = PowerSeries.C z.val * series I := rfl

@[simp] theorem constantCoeff_coordinate (z : Surcomplex.{u}ˣ) :
    (coordinate z).val.constantCoeff = z.val := by simp

@[simp] theorem coeff_one_coordinate (z : Surcomplex.{u}ˣ) :
    (coordinate z).val.coeff 1 = z.val * I := by
  rw [coordinate_val, PowerSeries.coeff_C_mul, coeff_one_series]

/-- Every integer frequency is an ordinary exponential germ times its actual phase coefficient. -/
theorem coordinate_zpow (z : Surcomplex.{u}ˣ) (k : ℤ) :
    (coordinate z ^ k).val = PowerSeries.C (z ^ k).val *
      PowerSeries.map ofComplex (series ((k : ℂ) * Complex.I)) := by
  rw [coordinate, mul_zpow, Units.val_mul, ← map_zpow,
    exponentialUnit_zpow, exponentialUnit_val, map_series, map_mul, map_intCast, ofComplex_I]
  rfl

/-- The actual formal angular germ of a Fourier coefficient window at a nonzero base coordinate. -/
def localSeries (N : ℕ) (c : ℤ → Surcomplex.{u}) (z : Surcomplex.{u}ˣ) :
    PowerSeries Surcomplex.{u} := LaurentCoordinateMultiplicity.localSeries N c (coordinate z)

/-- Frequency-wise ordinary-series expression, valid for arbitrary-size actual coefficients. -/
theorem localSeries_eq_sum (N : ℕ) (c : ℤ → Surcomplex.{u}) (z : Surcomplex.{u}ˣ) :
    localSeries N c z = ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
      PowerSeries.C (c k * (z ^ k).val) *
        PowerSeries.map ofComplex (series ((k : ℂ) * Complex.I)) := by
  unfold localSeries LaurentCoordinateMultiplicity.localSeries
  apply Finset.sum_congr rfl
  intro k _
  rw [coordinate_zpow, ← mul_assoc, ← map_mul]

/-- The angular germ of a native Laurent polynomial, independent of any chosen frequency bound. -/
def germ (p : LaurentPolynomial Surcomplex.{u}) (z : Surcomplex.{u}ˣ) :
    PowerSeries Surcomplex.{u} := p.smeval (coordinate z)

/-- Padding a frequency window with zero coefficients leaves the native angular germ unchanged. -/
theorem germ_eq_localSeries (p : LaurentPolynomial Surcomplex.{u})
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) (z : Surcomplex.{u}ˣ) :
    germ p z = localSeries N p.coeff z := by
  classical
  have hsub : p.coeff.support ⊆ Finset.Icc (-(N : ℤ)) N := by
    intro k hk
    have hb := hN k hk
    exact Finset.mem_Icc.mpr (by omega)
  unfold germ LaurentPolynomial.smeval localSeries LaurentCoordinateMultiplicity.localSeries
  simp only [Finsupp.sum, PowerSeries.smul_eq_C_mul]
  apply Finset.sum_subset hsub
  intro k _ hk
  rw [Finsupp.notMem_support_iff.mp hk, map_zero, zero_mul]

/-- Every nonzero Laurent polynomial has exactly its polynomial multiplicity in the angular germ. -/
theorem order_localSeries (N : ℕ) (c : ℤ → Surcomplex.{u}) (z : Surcomplex.{u}ˣ)
    (hp : LaurentAlgebraization.polynomial N c ≠ 0) :
    (localSeries N c z).order =
      ((LaurentAlgebraization.polynomial N c).rootMultiplicity z.val : ℕ∞) := by
  apply LaurentCoordinateMultiplicity.order_localSeries N c hp (coordinate z) z.val
    (constantCoeff_coordinate z)
  rw [coeff_one_coordinate]
  exact mul_ne_zero z.ne_zero (by
    intro h
    have hi := congrArg (fun w : Surcomplex.{u} => w.im) h
    simp at hi)

/-- Native Laurent-polynomial coefficients satisfy the same multiplicity identity at every finite angle. -/
theorem order_at_finite_angle (p : LaurentPolynomial Surcomplex.{u}) (hp : p ≠ 0)
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N)
    (θ : SignSequence.FiniteElement.{u}) :
    (localSeries N p.coeff (phaseUnit θ)).order =
      ((LaurentAlgebraization.polynomial N p.coeff).rootMultiplicity (finitePhase θ) : ℕ∞) := by
  apply order_localSeries
  rw [ne_eq, LaurentAlgebraization.polynomial_eq_zero_iff]
  obtain ⟨k, hk, hc⟩ := exists_laurent_coefficient_ne_zero p hp N hN
  exact fun h => hc (h k hk)

/-- The bound-independent native germ has the cleared polynomial's multiplicity at a finite angle. -/
theorem order_germ_at_finite_angle (p : LaurentPolynomial Surcomplex.{u}) (hp : p ≠ 0)
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N)
    (θ : SignSequence.FiniteElement.{u}) :
    (germ p (phaseUnit θ)).order =
      ((LaurentAlgebraization.polynomial N p.coeff).rootMultiplicity (finitePhase θ) : ℕ∞) := by
  rw [germ_eq_localSeries p N hN, order_at_finite_angle p hp N hN]

end
end Surreal.Surcomplex.AngularLaurent
