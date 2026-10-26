import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! New proof kernels for the 2026-10-26 continuation report.
These kernels do not assume primality or any exact order computation.
-/

namespace ProofSimplification20261026

/-- A single fixed-point identity controls the complete tower of exponents. -/
theorem fixed_power {M : Type*} [Monoid M] {x : M} {a : ℕ}
    (h : x ^ a = x) (n : ℕ) : x ^ (a ^ n) = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, ih, h]

/-- Coprimality depends only on the residue class, including modulus zero. -/
theorem coprime_of_cast_eq {a b m : ℕ}
    (h : (a : ZMod m) = (b : ZMod m)) (hb : Nat.Coprime b m) :
    Nat.Coprime a m := by
  apply (ZMod.isUnit_iff_coprime a m).mp
  rw [h]
  exact (ZMod.isUnit_iff_coprime b m).mpr hb

/-- The fixed modulus d*p certifies units for every d*p^n, including n=0. -/
theorem coprime_power_modulus {a b d p n : ℕ}
    (h : (a : ZMod (d * p)) = (b : ZMod (d * p)))
    (hb : Nat.Coprime b (d * p)) : Nat.Coprime a (d * p ^ n) := by
  have h0 := coprime_of_cast_eq h hb
  have hh : Nat.Coprime a d ∧ Nat.Coprime a p :=
    Nat.coprime_mul_iff_right.mp h0
  exact hh.1.mul_right (hh.2.pow_right n)

/-- Uniform polynomial specialization after the scalar fixed-point law. -/
theorem gamma_specialization {R : Type*} [CommRing R]
    (r b k : R) (a e rw n : ℕ) (h : b ^ a = b) :
    r ^ e * ((b ^ (a ^ n)) ^ 2 - 1) *
      (1 + b ^ (a ^ n) * (k + b ^ (a ^ rw))) =
    r ^ e * (b ^ 2 - 1) * (1 + b * (k + b)) := by
  simp only [fixed_power h]

/-- The old induction is a quadratic inequality in the single variable 4^r. -/
theorem sixteen_pow_bound_quadratic {r : ℕ} (hr : 2 ≤ r) :
    2 ^ (2 * r + 2) + 2 ≤ 16 ^ r := by
  have ht : 16 ≤ 4 ^ r := by
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 4) hr)
  have hleft : 2 ^ (2 * r + 2) = 4 * 4 ^ r := by
    rw [pow_add, pow_mul]
    norm_num
    ring
  have hright : 16 ^ r = (4 ^ r) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm r 2, pow_mul]
    norm_num
  rw [hleft, hright]
  nlinarith

/-- Compact drop-in body, retaining the old theorem's type. -/
theorem sixteen_pow_bound_short {r : ℕ} (hr : 2 ≤ r) :
    2 ^ (2 * r + 2) + 2 ≤ 16 ^ r := by
  have ht : 16 ≤ 4 ^ r := by
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 4) hr)
  have h : 4 ^ r * 4 + 2 ≤ 4 ^ r * 4 ^ r := by nlinarith
  simpa [pow_add, pow_mul, ← mul_pow] using h

#print axioms fixed_power
#print axioms coprime_power_modulus
#print axioms gamma_specialization
#print axioms sixteen_pow_bound_quadratic
#print axioms sixteen_pow_bound_short

end ProofSimplification20261026
