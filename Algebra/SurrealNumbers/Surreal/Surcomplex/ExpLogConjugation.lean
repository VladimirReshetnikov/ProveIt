import Surreal.Surcomplex.ExpLog
import Surreal.Surcomplex.StrongConjugation

/-!
# Conjugation and the infinitesimal unit-circle logarithm

The remaining conjugation and unit-circle clauses of `e:prop-infexp` hold
for the actual surcomplex strong sums. Conjugation commutes with evaluation
because the formal exponential and logarithm have rational coefficients.
The logarithm of a modulus-one element infinitesimally close to one has
zero real part. This is local to the infinitesimal domain.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Actual infinitesimal exponential commutes with conjugation. -/
theorem infExp_conj (x : Surcomplex.{u}) (hx : IsInfinitesimal x) :
    infExp (conj x) (infinitesimal_conj hx) = conj (infExp x hx) := by
  simpa only [infExp, PowerSeries.map_exp] using
    powerSeriesEvaluation_conj x hx (PowerSeries.exp ℂ)

/-- The actual logarithm of one plus an infinitesimal commutes with conjugation. -/
theorem infLog_conj (x : Surcomplex.{u}) (hx : IsInfinitesimal x) :
    infLog (conj x) (infinitesimal_conj hx) = conj (infLog x hx) := by
  simpa only [infLog, PowerSeries.map_log] using
    powerSeriesEvaluation_conj x hx (PowerSeries.log ℂ)

/-- A near-one element satisfying the algebraic unit-circle identity has
an anti-invariant logarithm under conjugation. -/
theorem conj_infLog_eq_neg_of_mul_conj_eq_one (z : Surcomplex.{u})
    (hz : IsInfinitesimal (z - 1)) (hunit : z * conj z = 1) :
    conj (infLog (z - 1) hz) = -infLog (z - 1) hz := by
  have h := infLog_mul (z - 1) (conj (z - 1)) hz (infinitesimal_conj hz)
  rw [infLog_conj (z - 1) hz] at h
  have he : (1 + (z - 1)) * (1 + conj (z - 1)) - 1 = 0 := by
    simp only [map_sub, map_one, add_sub_cancel, hunit, sub_self]
  have hh : infLog (z - 1) hz + conj (infLog (z - 1) hz) = 0 := by
    rw [← h]
    simp only [he, infLog_zero]
  exact eq_neg_of_add_eq_zero_right hh

/-- The logarithm in the preceding statement has zero actual real coordinate. -/
theorem infLog_re_eq_zero_of_mul_conj_eq_one (z : Surcomplex.{u})
    (hz : IsInfinitesimal (z - 1)) (hunit : z * conj z = 1) :
    (infLog (z - 1) hz).re = 0 := by
  have h := congrArg (fun w : Surcomplex.{u} => w.re)
    (conj_infLog_eq_neg_of_mul_conj_eq_one z hz hunit)
  rw [conj_re] at h
  change (infLog (z - 1) hz).re = -(infLog (z - 1) hz).re at h
  linarith

/-- The literal modulus-one clause of `e:prop-infexp` for actual surcomplex numbers. -/
theorem infLog_re_eq_zero_of_modulus_eq_one (z : Surcomplex.{u})
    (hz : IsInfinitesimal (z - 1)) (hunit : modulus z = 1) :
    (infLog (z - 1) hz).re = 0 := by
  apply infLog_re_eq_zero_of_mul_conj_eq_one z hz
  rw [mul_conj, ← modulus_sq, hunit, one_pow, map_one]

end
end Surreal.Surcomplex
