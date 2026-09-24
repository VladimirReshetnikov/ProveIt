import Surreal.Algebra.PowerDifferenceFactors
import Surreal.Foundations.OmnificPowerRigidity
import Surreal.Foundations.OmnificRealScaling
import Surreal.Foundations.OmnificConstantRigidity
import Surreal.Surcomplex.BinaryFormRigidity
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Omnific rigidity for differences of powers with a common exponent divisor

The equal-power clause of `odg:cor:thue` and the positive-exponent form of
`odg:rem:powers` (also `odg:cor:powers`). Mathlib's complex primitive roots
of unity give two projective factors. The common-divisor reduction then
uses univariate rigidity to recover the original bases. Zero exponents
must be excluded: omega^0 - 0^2 = 1 is a counterexample to the literal
remark with unrestricted nonnegative exponents.
-/

universe u
namespace Surreal.Surcomplex

open Foundations BinaryFormRigidity MvPolynomial

noncomputable section

/-- Every complex power difference of degree at least two has two distinct projective factors. -/
theorem complex_powerDifference_hasTwoProjectiveFactors (d : ℕ) (hd : 2 ≤ d) :
    HasTwoProjectiveFactors (powerDifference (R := ℂ) d) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨r, hr⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ d
  exact powerDifference_hasTwoProjectiveFactors d r hr.pow_eq_one (hr.ne_one (by omega))

/-- Equal-power equations at nonzero ordinary levels force ordinary omnific coordinates. -/
theorem omnific_equal_powers_rigidity (d : ℕ) (hd : 2 ≤ d) (c : ℤ) (hc : c ≠ 0)
    (x y : SignSequence.OmnificInteger.{u})
    (h : x ^ d - y ^ d = SignSequence.omnificIntCast c) :
    x = SignSequence.omnificIntCast (SignSequence.omnificConstantCoeff x) ∧
      y = SignSequence.omnificIntCast (SignSequence.omnificConstantCoeff y) := by
  let v : Fin 2 → SignSequence.OmnificInteger := ![x, y]
  have hp : HasTwoProjectiveFactors
      ((powerDifference (R := ℤ) d).map (Int.castRingHom ℂ)) := by
    simpa only [powerDifference, map_sub, map_pow, map_X] using
      complex_powerDifference_hasTwoProjectiveFactors d hd
  have he : (powerDifference (R := ℤ) d).eval₂ SignSequence.omnificIntCast v =
      SignSequence.omnificIntCast c := by
    simpa only [powerDifference, eval₂_sub, eval₂_pow, eval₂_X,
      v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] using h
  obtain ⟨a, _, ha⟩ := (omnific_integer_binary_solutions_iff _ hp c hc v).mp he
  have hconst (k : Fin 2) : v k =
      SignSequence.omnificIntCast (SignSequence.omnificConstantCoeff (v k)) := by
    rw [ha k, SignSequence.omnificConstantCoeff_intCast]
  exact ⟨hconst 0, hconst 1⟩

/-- Reduction through any common divisor greater than one, with both original exponents positive. -/
theorem omnific_common_divisor_powers_rigidity (m n d : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hd : 2 ≤ d) (hdm : d ∣ m) (hdn : d ∣ n) (c : ℤ) (hc : c ≠ 0)
    (x y : SignSequence.OmnificInteger.{u})
    (h : x ^ m - y ^ n = SignSequence.omnificIntCast c) :
    x = SignSequence.omnificIntCast (SignSequence.omnificConstantCoeff x) ∧
      y = SignSequence.omnificIntCast (SignSequence.omnificConstantCoeff y) := by
  obtain ⟨a, rfl⟩ := hdm
  obtain ⟨b, rfl⟩ := hdn
  have ha : 0 < a := Nat.pos_of_mul_pos_left hm
  have hb : 0 < b := Nat.pos_of_mul_pos_left hn
  have he : (x ^ a) ^ d - (y ^ b) ^ d = SignSequence.omnificIntCast c := by
    simpa only [← pow_mul, Nat.mul_comm a d, Nat.mul_comm b d] using h
  obtain ⟨hx, hy⟩ := omnific_equal_powers_rigidity d hd c hc (x ^ a) (y ^ b) he
  exact ⟨SignSequence.omnific_eq_intConstant_of_pow x a ha _ hx,
    SignSequence.omnific_eq_intConstant_of_pow y b hb _ hy⟩

/-- Exact equality with the ordinary integer solution set when the positive exponents have
gcd greater than one. -/
theorem omnific_gcd_powers_solutions_iff (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hg : 1 < Nat.gcd m n) (c : ℤ) (hc : c ≠ 0) (x y : SignSequence.OmnificInteger.{u}) :
    x ^ m - y ^ n = SignSequence.omnificIntCast c ↔
      ∃ a b : ℤ, a ^ m - b ^ n = c ∧
        x = SignSequence.omnificIntCast a ∧ y = SignSequence.omnificIntCast b := by
  constructor
  · intro h
    have he := omnific_common_divisor_powers_rigidity m n (Nat.gcd m n) hm hn hg
      (Nat.gcd_dvd_left m n) (Nat.gcd_dvd_right m n) c hc x y h
    refine ⟨SignSequence.omnificConstantCoeff x, SignSequence.omnificConstantCoeff y, ?_, he⟩
    simpa only [map_sub, map_pow, SignSequence.omnificConstantCoeff_intCast] using
      congrArg SignSequence.omnificConstantCoeff h
  · rintro ⟨a, b, he, rfl, rfl⟩
    rw [← map_pow, ← map_pow, ← map_sub, he]

/-- Allowing a zero exponent invalidates the gcd-only version: omega^0 - 0^2 = 1. -/
theorem omnific_zero_exponent_counterexample :
    1 < Nat.gcd 0 2 ∧ ∃ x y : SignSequence.OmnificInteger.{u},
      x ^ 0 - y ^ 2 = SignSequence.omnificIntCast 1 ∧
        ¬ SignSequence.IsFinite (SignSequence.omnificToSurreal x) := by
  refine ⟨by decide, SignSequence.omnificMonomial 1 zero_lt_one, 0, by simp, ?_⟩
  exact SignSequence.omnific_purelyInfinite_not_finite _
    (SignSequence.omnificMonomial_mem_purelyInfinite 1 zero_lt_one)
    (SignSequence.omnificMonomial_ne_zero 1 zero_lt_one)

end
end Surreal.Surcomplex
