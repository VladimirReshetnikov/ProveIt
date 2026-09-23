import Surreal.Surcomplex.AngularLaurentSeries
import Surreal.Surcomplex.StrongSeriesFinite

/-!
# Exact strong evaluation of angular Laurent germs

The local formal series for every finite Laurent sum represents its actual
values after `z ↦ z Ex(ih)` at all infinitesimal complex increments. Finite
coefficient sums allow arbitrary infinite surcomplex coefficients. This
supplies the strong-series interpretation of the multiplicity bridge for
`trigonometry:thm:polyroots`.
-/

universe u
namespace Surreal.Surcomplex.AngularLaurent

open Foundations FormalExponentialCoordinate

noncomputable section

/-- The ordinary formal exponential germ evaluates to the actual infinitesimal phase. -/
theorem evaluation_series_I (h : Surcomplex.{u}) (hh : IsInfinitesimal h) :
    powerSeriesEvaluation h hh (series Complex.I) = infinitesimalPhase h hh := by
  rw [series, PowerSeries.rescale_eq_subst, PowerSeries.smul_eq_C_mul,
    powerSeriesEvaluation_subst_const_mul_X h hh Complex.I _
      (by simpa only [ofComplex_I] using infinitesimal_I_mul hh)]
  simp only [ofComplex_I, infinitesimalPhase, infExp]

/-- Every integer frequency has the expected actual phase power. -/
theorem evaluation_frequency (h : Surcomplex.{u}) (hh : IsInfinitesimal h) (k : ℤ) :
    powerSeriesEvaluation h hh (series ((k : ℂ) * Complex.I)) = infinitesimalPhase h hh ^ k := by
  have he := congrArg Units.val
    (map_zpow (Units.map (powerSeriesEvaluation h hh).toMonoidHom)
      (exponentialUnit Complex.I) k)
  simp only [exponentialUnit_zpow, Units.coe_map, exponentialUnit_val,
    Units.val_zpow_eq_zpow_val] at he
  change powerSeriesEvaluation h hh (series ((k : ℂ) * Complex.I)) =
    powerSeriesEvaluation h hh (series Complex.I) ^ k at he
  rw [evaluation_series_I] at he
  exact he

/-- The literal angular-series terms form a strong sum equal to the actual Laurent value. -/
theorem strongSum_localSeries (N : ℕ) (c : ℤ → Surcomplex.{u}) (z : Surcomplex.{u}ˣ)
    (h : Surcomplex.{u}) (hh : IsInfinitesimal h) :
    ∃ hs : StronglySummable (fun n => (localSeries N c z).coeff n * h ^ n),
      strongSum _ hs = FiniteFourier.laurentEval N c (z.val * infinitesimalPhase h hh) := by
  classical
  rw [localSeries_eq_sum]
  unfold FiniteFourier.laurentEval
  apply strongSeries_finset_sum _ _ _ h hh
  intro k _
  obtain ⟨hs, he⟩ := strongSeries_scalar (c k * (z ^ k).val) h hh
    (series ((k : ℂ) * Complex.I))
  refine ⟨hs, ?_⟩
  rw [he, evaluation_frequency, Units.val_zpow_eq_zpow_val, mul_zpow]
  ring

/-- At a real infinitesimal increment the complex local phase is the established finite real phase. -/
theorem infinitesimalPhase_ofReal (h : SignSequence.FiniteElement.{u})
    (hc : IsInfinitesimal (ofReal h.val)) :
    infinitesimalPhase (ofReal h.val) hc = finitePhase h := by
  rw [infinitesimalPhase_eq_finiteExp, finitePhase]
  congr 1
  apply Subtype.ext
  change I * ofReal h.val = ofReal h.val * I
  exact mul_comm _ _

/-- The formal germ at every finite real angle is an exact strong expansion of the native function. -/
theorem strongSum_at_finite_angle (p : LaurentPolynomial Surcomplex.{u})
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N)
    (θ h : SignSequence.FiniteElement.{u}) (hh : SignSequence.IsInfinitesimal h.val) :
    ∃ hs : StronglySummable
      (fun n => (localSeries N p.coeff (phaseUnit θ)).coeff n * (ofReal h.val) ^ n),
      strongSum _ hs = trigonometricPolynomial p (θ + h) := by
  have hc : IsInfinitesimal (ofReal h.val) := by
    exact ⟨by simpa using hh, by simp [Foundations.SignSequence.infinitesimal_zero]⟩
  obtain ⟨hs, he⟩ := strongSum_localSeries N p.coeff (phaseUnit θ) (ofReal h.val) hc
  refine ⟨hs, ?_⟩
  rw [he, infinitesimalPhase_ofReal h hc, phaseUnit_val, ← finitePhase_add,
    ← trigonometricPolynomial_eq_laurentSum p N hN]

/-- The bound-independent native angular germ strongly evaluates to the original trigonometric function. -/
theorem strongSum_germ_at_finite_angle (p : LaurentPolynomial Surcomplex.{u})
    (θ h : SignSequence.FiniteElement.{u}) (hh : SignSequence.IsInfinitesimal h.val) :
    ∃ hs : StronglySummable
      (fun n => (germ p (phaseUnit θ)).coeff n * (ofReal h.val) ^ n),
      strongSum _ hs = trigonometricPolynomial p (θ + h) := by
  obtain ⟨N, hN⟩ := LaurentCayley.exists_frequency_bound p
  rw [germ_eq_localSeries p N hN]
  exact strongSum_at_finite_angle p N hN θ h hh

/-- The total native orders of the verified angular germs satisfy the `2N` root bound. -/
theorem sum_angular_orders_le (p : LaurentPolynomial Surcomplex.{u}) (hp : p ≠ 0)
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N)
    (S : Finset SignSequence.FiniteElement.{u})
    (hS : ∀ θ ∈ S, trigonometricPolynomial p θ = 0)
    (hinj : Set.InjOn finitePhase (S : Set SignSequence.FiniteElement.{u})) :
    ∑ θ ∈ S, (germ p (phaseUnit θ)).order.toNat ≤ 2 * N := by
  have h := sum_laurentSum_rootMultiplicities_le N p.coeff
    (exists_laurent_coefficient_ne_zero p hp N hN) S
    (fun θ hθ => by rw [← trigonometricPolynomial_eq_laurentSum p N hN]; exact hS θ hθ) hinj
  simpa only [order_germ_at_finite_angle p hp N hN, ENat.toNat_coe] using h

end
end Surreal.Surcomplex.AngularLaurent
