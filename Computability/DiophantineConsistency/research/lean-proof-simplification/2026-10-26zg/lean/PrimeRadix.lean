import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Lean.Elab.Tactic.Omega

/-!
A standalone arithmetic boundary for NativeBinaryScale.
No project theorem is imported, and no source-system or machine condition is
assumed. The hypotheses are exactly prime-power divisibility and divisibility
of q - 1 by a block-radix minus one.
-/
namespace PrimeRadix

/-- Divisibility between repunit numerators detects exponent divisibility. -/
theorem exponent_dvd_of_pow_sub_one_dvd {p d u : Nat} (hp : 1 < p)
    (h : p ^ d - 1 ∣ p ^ u - 1) : d ∣ u := by
  have hm := Nat.mod_eq_zero_of_dvd h
  rw [Nat.pow_sub_one_mod_pow_sub_one] at hm
  apply Nat.dvd_of_mod_eq_zero
  by_contra hn
  have hsmall := (Nat.pow_le_one_iff hn).mp (Nat.sub_eq_zero_iff_le.mp hm)
  omega

/-- A prime-power divisor with the block congruence is already a block power.
The theorem also supplies the source's exponent budget without a second cast
or an intermediate existential binary exponent at its client. -/
theorem block_power_of_prime_power_divisor {p d q R : Nat}
    (hp : Nat.Prime p) (hq : 1 < q)
    (hdiv : q ∣ p ^ R) (hblock : p ^ d - 1 ∣ q - 1) :
    ∃ N, 0 < N ∧ d * N ≤ R ∧ q = (p ^ d) ^ N := by
  obtain ⟨u, hu, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdiv
  obtain ⟨N, rfl⟩ := exponent_dvd_of_pow_sub_one_dvd hp.one_lt hblock
  refine ⟨N, ?_, hu, pow_mul p d N⟩
  by_contra hn
  have hzero : N = 0 := by omega
  simp only [hzero, Nat.mul_zero, pow_zero] at hq
  omega

/-- Affine form matching sourceQ = 1 + J * beta, beta = p^d - 1. -/
theorem block_power_of_affine_certificate {p d q J R : Nat}
    (hp : Nat.Prime p) (hq : 1 < q) (hdiv : q ∣ p ^ R)
    (hsource : q = 1 + J * (p ^ d - 1)) :
    ∃ N, 0 < N ∧ d * N ≤ R ∧ q = (p ^ d) ^ N := by
  apply block_power_of_prime_power_divisor hp hq hdiv
  rw [hsource, Nat.add_sub_cancel_left]
  exact dvd_mul_left _ _

#print axioms exponent_dvd_of_pow_sub_one_dvd
#print axioms block_power_of_prime_power_divisor
#print axioms block_power_of_affine_certificate

example : ∃ N, 0 < N ∧ 3 * N ≤ 12 ∧ 64 = (2 ^ 3) ^ N :=
  block_power_of_prime_power_divisor (by decide) (by decide) (by decide) (by decide)

-- The exponent-zero input q=1 is deliberately excluded by 1<q.
-- The theorem itself also handles d=0 correctly: its other premises become
-- incompatible, so no spurious positive cell count is asserted.

end PrimeRadix
