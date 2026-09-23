import Surreal.Surcomplex.PowerSeries
import Surreal.Foundations.SignSequencePowerSeries
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Finite remainders after arbitrary formal truncations

At an actual infinitesimal, the tail after degree `n - 1` is `x^n` times a
finite element whose standard part is coefficient `n`. This gives the exact
algebraic meaning of the remainder notation in `trigonometry:prop:leading`.
-/

universe u

namespace Surreal.Foundations.SignSequence

/-- Evaluation of an ordinary polynomial truncation is its finite coefficient sum. -/
theorem powerSeriesEvaluation_trunc (x : SignSequence.{u}) (hx : IsInfinitesimal x)
    (f : PowerSeries ℝ) (n : ℕ) :
    powerSeriesEvaluation x hx (PowerSeries.trunc n f) =
      ∑ k ∈ Finset.range n, ofReal (f.coeff k) * x ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [PowerSeries.trunc_succ, Polynomial.coe_add, Polynomial.coe_monomial,
      map_add, PowerSeries.monomial_eq_C_mul_X_pow, map_mul, map_pow,
      powerSeriesEvaluation_C, powerSeriesEvaluation_X, Finset.sum_range_succ, ih]

/-- Every finite Taylor truncation has a finite normalized tail of known residue. -/
theorem exists_finite_powerSeries_remainder (x : SignSequence.{u}) (hx : IsInfinitesimal x)
    (f : PowerSeries ℝ) (n : ℕ) :
    ∃ R : SignSequence.{u}, IsFinite R ∧ standardPart R = f.coeff n ∧
      powerSeriesEvaluation x hx f =
        (∑ k ∈ Finset.range n, ofReal (f.coeff k) * x ^ k) + x ^ n * R := by
  refine ⟨powerSeriesEvaluation x hx (PowerSeries.mk (fun k => f.coeff (k + n))),
    isFinite_powerSeriesEvaluation x hx _, ?_, ?_⟩
  · rw [standardPart_powerSeriesEvaluation, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_mk, Nat.zero_add]
  · have h := congrArg (powerSeriesEvaluation x hx)
      (PowerSeries.eq_X_pow_mul_shift_add_trunc n f)
    simpa only [map_add, map_mul, map_pow, powerSeriesEvaluation_X,
      powerSeriesEvaluation_trunc, add_comm] using h

end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

/-- Evaluation of an ordinary polynomial truncation is its finite coefficient sum. -/
theorem powerSeriesEvaluation_trunc (x : Surcomplex.{u}) (hx : IsInfinitesimal x)
    (f : PowerSeries ℂ) (n : ℕ) :
    powerSeriesEvaluation x hx (PowerSeries.trunc n f) =
      ∑ k ∈ Finset.range n, ofComplex (f.coeff k) * x ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [PowerSeries.trunc_succ, Polynomial.coe_add, Polynomial.coe_monomial,
      map_add, PowerSeries.monomial_eq_C_mul_X_pow, map_mul, map_pow,
      powerSeriesEvaluation_C, powerSeriesEvaluation_X, Finset.sum_range_succ, ih]

/-- Every finite Taylor truncation has a finite normalized tail of known residue. -/
theorem exists_finite_powerSeries_remainder (x : Surcomplex.{u}) (hx : IsInfinitesimal x)
    (f : PowerSeries ℂ) (n : ℕ) :
    ∃ R : Surcomplex.{u}, IsFinite R ∧ standardPart R = f.coeff n ∧
      powerSeriesEvaluation x hx f =
        (∑ k ∈ Finset.range n, ofComplex (f.coeff k) * x ^ k) + x ^ n * R := by
  refine ⟨powerSeriesEvaluation x hx (PowerSeries.mk (fun k => f.coeff (k + n))),
    isFinite_powerSeriesEvaluation x hx _, ?_, ?_⟩
  · rw [standardPart_powerSeriesEvaluation, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_mk, Nat.zero_add]
  · have h := congrArg (powerSeriesEvaluation x hx)
      (PowerSeries.eq_X_pow_mul_shift_add_trunc n f)
    simpa only [map_add, map_mul, map_pow, powerSeriesEvaluation_X,
      powerSeriesEvaluation_trunc, add_comm] using h

end Surreal.Surcomplex
