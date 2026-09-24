import Surreal.HahnSeries.ExponentialAddition
import Surreal.HahnSeries.CoefficientMapping
import Surreal.HahnSeries.ComplexNumbers

/-!
# Coefficient maps and conjugation commute with infinitesimal exp/log

The displayed exponential and logarithmic Hahn sums are natural under
coefficient field homomorphisms. In particular, native complex conjugation
commutes with them. A near-one series of norm one has purely imaginary
logarithm, as asserted in `e:prop-infexp` of the analysis report.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ K L : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K] [CharZero K] [Field L] [CharZero L]

/-- Infinitesimal exponential commutes with coefficient field maps. -/
theorem mapCoefficients_infExp (f : K →+* L) (x : K⟦Γ⟧) (hx : 0 < x.orderTop) :
    mapCoefficients f (infExp x hx) =
      infExp (mapCoefficients f x) (orderTop_mapCoefficients_pos f x hx) := by
  unfold infExp
  rw [mapCoefficients_evaluate, PowerSeries.map_exp]

/-- The logarithm of `1 + x` commutes with coefficient field maps. -/
theorem mapCoefficients_infLog (f : K →+* L) (x : K⟦Γ⟧) (hx : 0 < x.orderTop) :
    mapCoefficients f (infLog x hx) =
      infLog (mapCoefficients f x) (orderTop_mapCoefficients_pos f x hx) := by
  unfold infLog
  rw [mapCoefficients_evaluate, PowerSeries.map_log]

/-- Ordinary complex conjugation commutes with infinitesimal exponential. -/
theorem complexConjugation_infExp (x : ℂ⟦Γ⟧) (hx : 0 < x.orderTop) :
    complexConjugation (infExp x hx) =
      infExp (complexConjugation x) (by simpa using hx) :=
  mapCoefficients_infExp (starRingAut : ℂ ≃+* ℂ).toRingHom x hx

/-- Ordinary complex conjugation commutes with the logarithm of `1 + x`. -/
theorem complexConjugation_infLog (x : ℂ⟦Γ⟧) (hx : 0 < x.orderTop) :
    complexConjugation (infLog x hx) =
      infLog (complexConjugation x) (by simpa using hx) :=
  mapCoefficients_infLog (starRingAut : ℂ ≃+* ℂ).toRingHom x hx

/-- For a near-one series satisfying `z * conj z = 1`, conjugation negates
its infinitesimal logarithm. This is the unit-circle clause of `e:prop-infexp`. -/
theorem complexConjugation_infLog_eq_neg_of_mul_conj_eq_one (z : ℂ⟦Γ⟧)
    (hz : 0 < (z - 1).orderTop) (hnorm : z * complexConjugation z = 1) :
    complexConjugation (infLog (z - 1) hz) = -infLog (z - 1) hz := by
  have hlog := infLog_orderTop_pos (z - 1) hz
  apply infExp_injective (by simpa using hlog) (by simpa using hlog)
  rw [← complexConjugation_infExp _ hlog, infExp_neg _ hlog,
    infExp_infLog, add_sub_cancel]
  exact eq_inv_of_mul_eq_one_right hnorm

/-- Every coefficient of this logarithm has zero real part. -/
theorem infLog_re_eq_zero_of_mul_conj_eq_one (z : ℂ⟦Γ⟧)
    (hz : 0 < (z - 1).orderTop) (hnorm : z * complexConjugation z = 1) (g : Γ) :
    ((infLog (z - 1) hz).coeff g).re = 0 := by
  have h := congrArg (fun w : ℂ⟦Γ⟧ => (w.coeff g).re)
    (complexConjugation_infLog_eq_neg_of_mul_conj_eq_one z hz hnorm)
  simp only [coeff_complexConjugation, Complex.star_def, Complex.conj_re,
    coeff_neg, Complex.neg_re] at h
  linarith

end
end Surreal.HahnSeries
