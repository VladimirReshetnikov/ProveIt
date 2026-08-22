import Mathlib.NumberTheory.FermatPsp
import Mathlib.Data.ZMod.Basic

/-!
# The first Fermat-quotient determinant layer

This module formalizes the elementary modular layer that precedes any use of
the Iwasawa logarithm.  For a prime `p` not dividing `u`, the natural Fermat
quotient is `(u^(p-1)-1)/p`.  We prove its exact defining identity, its power
law modulo `p`, and the vanishing of the two-by-two Fermat-quotient determinant
on every common integral power pair `(2^n, 3^n)`.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open scoped BigOperators

/-- The natural representative of the Fermat quotient.  The expected divisibility is
proved separately under primality and coprimality hypotheses. -/
def fermatQuotientNat (p u : ℕ) : ℕ :=
  (u ^ (p - 1) - 1) / p

/-- Fermat's little theorem in the exact divisibility form needed to justify the quotient. -/
theorem prime_dvd_pow_sub_one {p u : ℕ} (hp : p.Prime) (hpu : ¬p ∣ u) :
    p ∣ u ^ (p - 1) - 1 := by
  have hu0 : u ≠ 0 := by
    intro hu
    apply hpu
    simp [hu]
  have hone : 1 ≤ u ^ (p - 1) := Nat.pow_pos (Nat.pos_of_ne_zero hu0)
  have hcop : p.Coprime u := (hp.coprime_iff_not_dvd).2 hpu
  have hcopInt : IsCoprime (u : ℤ) (p : ℤ) := hcop.symm.isCoprime
  have hmod : (u : ℤ) ^ (p - 1) ≡ 1 [ZMOD (p : ℤ)] :=
    Int.ModEq.pow_card_sub_one_eq_one hp hcopInt
  have hdvd : (p : ℤ) ∣ (u : ℤ) ^ (p - 1) - 1 :=
    Int.ModEq.dvd hmod.symm
  have hdvd' : (p : ℤ) ∣ ((u ^ (p - 1) - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hone, Nat.cast_pow, Nat.cast_one]
    exact hdvd
  exact_mod_cast hdvd'

/-- Exact integral identity defining the Fermat quotient. -/
theorem pow_eq_one_add_mul_fermatQuotientNat {p u : ℕ}
    (hp : p.Prime) (hpu : ¬p ∣ u) :
    u ^ (p - 1) = 1 + p * fermatQuotientNat p u := by
  have hu0 : u ≠ 0 := by
    intro hu
    apply hpu
    simp [hu]
  have hone : 1 ≤ u ^ (p - 1) := Nat.pow_pos (Nat.pos_of_ne_zero hu0)
  have hdvd := prime_dvd_pow_sub_one hp hpu
  calc
    u ^ (p - 1) = 1 + (u ^ (p - 1) - 1) :=
      (Nat.add_sub_of_le hone).symm
    _ = 1 + p * fermatQuotientNat p u := by
      rw [fermatQuotientNat, Nat.mul_div_cancel' hdvd]

private theorem fermatQuotientNat_pow_exact {p u n : ℕ}
    (hp : p.Prime) (hpu : ¬p ∣ u) :
    fermatQuotientNat p (u ^ n) =
      (∑ i ∈ Finset.range n, (u ^ (p - 1)) ^ i) * fermatQuotientNat p u := by
  let x := u ^ (p - 1)
  let q := fermatQuotientNat p u
  have hu0 : u ≠ 0 := by
    intro hu
    apply hpu
    simp [hu]
  have hxone : 1 ≤ x := by
    exact Nat.pow_pos (Nat.pos_of_ne_zero hu0)
  have hspec : x = 1 + p * q := by
    exact pow_eq_one_add_mul_fermatQuotientNat hp hpu
  have hxsub : x - 1 = p * q := by omega
  have hpow : (u ^ n) ^ (p - 1) = x ^ n := by
    calc
      (u ^ n) ^ (p - 1) = u ^ (n * (p - 1)) := (pow_mul u n (p - 1)).symm
      _ = u ^ ((p - 1) * n) := by rw [mul_comm n (p - 1)]
      _ = (u ^ (p - 1)) ^ n := pow_mul u (p - 1) n
  calc
    fermatQuotientNat p (u ^ n) = (x ^ n - 1) / p := by
      simp only [fermatQuotientNat, hpow]
    _ = ((∑ i ∈ Finset.range n, x ^ i) * (x - 1)) / p := by
      rw [geom_sum_mul_of_one_le hxone]
    _ = ((∑ i ∈ Finset.range n, x ^ i) * (p * q)) / p := by rw [hxsub]
    _ = (∑ i ∈ Finset.range n, x ^ i) * q := by
      rw [show (∑ i ∈ Finset.range n, x ^ i) * (p * q) =
          p * ((∑ i ∈ Finset.range n, x ^ i) * q) by ac_rfl]
      exact Nat.mul_div_cancel_left _ hp.pos

/-- The Fermat quotient as its canonical residue modulo `p`. -/
def fermatQuotientResidue (p u : ℕ) : ZMod p :=
  fermatQuotientNat p u

/-- The fundamental power rule `q_p(u^n) = n q_p(u) (mod p)`. -/
theorem fermatQuotientResidue_pow {p u n : ℕ}
    (hp : p.Prime) (hpu : ¬p ∣ u) :
    fermatQuotientResidue p (u ^ n) =
      (n : ZMod p) * fermatQuotientResidue p u := by
  have hspec := pow_eq_one_add_mul_fermatQuotientNat hp hpu
  have hxmod : (u : ZMod p) ^ (p - 1) = 1 := by
    rw [← Nat.cast_pow, hspec]
    push_cast
    simp
  rw [fermatQuotientResidue, fermatQuotientNat_pow_exact hp hpu]
  push_cast
  rw [hxmod]
  simp [fermatQuotientResidue]

/-- The first residue-level determinant attached to `(M,A)` and the base pair `(2,3)`. -/
def fermatQuotientDeterminant (p M A : ℕ) : ZMod p :=
  fermatQuotientResidue p M * fermatQuotientResidue p 3 -
    fermatQuotientResidue p A * fermatQuotientResidue p 2

/-- Any four first Iwasawa-logarithm residues satisfying `log_p(u)/p = -q_p(u)` have
determinant equal to the Fermat-quotient determinant.  This theorem is the exact algebraic
interface to the external p-adic logarithm congruence. -/
theorem firstLogDeterminant_eq_fermatQuotientDeterminant {p M A : ℕ}
    {lM lA lTwo lThree : ZMod p}
    (hM : lM = -fermatQuotientResidue p M)
    (hA : lA = -fermatQuotientResidue p A)
    (hTwo : lTwo = -fermatQuotientResidue p 2)
    (hThree : lThree = -fermatQuotientResidue p 3) :
    lM * lThree - lA * lTwo = fermatQuotientDeterminant p M A := by
  rw [hM, hA, hTwo, hThree]
  simp only [neg_mul_neg]
  rfl

/-- Every common integral power pair has zero Fermat-quotient determinant. -/
theorem fermatQuotientDeterminant_two_three_powers {p n : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    fermatQuotientDeterminant p (2 ^ n) (3 ^ n) = 0 := by
  have hp2 : ¬p ∣ 2 := by
    intro h
    have hle := Nat.le_of_dvd (by norm_num : 0 < 2) h
    omega
  have hp3 : ¬p ∣ 3 := by
    intro h
    have hle := Nat.le_of_dvd (by norm_num : 0 < 3) h
    omega
  rw [fermatQuotientDeterminant, fermatQuotientResidue_pow hp hp2,
    fermatQuotientResidue_pow hp hp3]
  ring

end LeanProofs.TwoBaseIntegerExponent
