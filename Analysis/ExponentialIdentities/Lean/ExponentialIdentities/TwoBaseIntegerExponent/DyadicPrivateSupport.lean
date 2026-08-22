import Mathlib

/-!
Finite modular core for the private odd-prime support of the dyadic factors
`T ^ (2 ^ j) + 1`.

The existence of an odd prime divisor and the resulting multiplicative-independence
package are elementary paper consequences.  This module isolates the order, congruence,
and privacy statements used by those consequences.
-/

namespace LeanProofs.TwoBaseIntegerExponent.DyadicPrivateSupport

variable {G : Type*} [Monoid G]

theorem orderOf_eq_two_pow_succ (g : G) (j : ℕ)
    (hnot : g ^ (2 ^ j) ≠ 1) (hfin : g ^ (2 ^ (j + 1)) = 1) :
    orderOf g = 2 ^ (j + 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow hnot hfin

theorem oddPrime_divisor_has_private_order
    {T q j : ℕ} (hq : q.Prime) (hqodd : q ≠ 2)
    (hdiv : q ∣ T ^ (2 ^ j) + 1) :
    orderOf (T : ZMod q) = 2 ^ (j + 1) := by
  letI : Fact q.Prime := ⟨hq⟩
  have hmod : T ^ (2 ^ j) + 1 ≡ 0 [MOD q] :=
    Nat.modEq_zero_iff_dvd.mpr hdiv
  have hz : ((T ^ (2 ^ j) + 1 : ℕ) : ZMod q) = 0 := by
    simpa only [Nat.cast_zero] using
      (ZMod.natCast_eq_natCast_iff (T ^ (2 ^ j) + 1) 0 q).2 hmod
  have hminus : (T : ZMod q) ^ (2 ^ j) = -1 := by
    push_cast at hz
    exact eq_neg_of_add_eq_zero_left hz
  have hnot : (T : ZMod q) ^ (2 ^ j) ≠ 1 := by
    rw [hminus]
    intro hneg
    have htwo : ((2 : ℕ) : ZMod q) = ((0 : ℕ) : ZMod q) := by
      have hadd := congrArg (fun z : ZMod q => z + 1) hneg
      calc
        ((2 : ℕ) : ZMod q) = (1 : ZMod q) + 1 := by norm_num
        _ = 0 := by simpa using hadd.symm
        _ = ((0 : ℕ) : ZMod q) := by simp
    have htwoMod : 2 ≡ 0 [MOD q] :=
      (ZMod.natCast_eq_natCast_iff 2 0 q).1 htwo
    have hqdvd2 : q ∣ 2 := Nat.modEq_zero_iff_dvd.mp htwoMod
    rcases (Nat.dvd_prime Nat.prime_two).mp hqdvd2 with hq1 | hq2
    · exact hq.ne_one hq1
    · exact hqodd hq2
  have hfin : (T : ZMod q) ^ (2 ^ (j + 1)) = 1 := by
    rw [pow_succ, pow_mul, hminus]
    norm_num
  exact orderOf_eq_two_pow_succ (T : ZMod q) j hnot hfin

theorem oddPrime_divisor_congruent_one
    {T q j : ℕ} (hq : q.Prime) (hqodd : q ≠ 2)
    (hdiv : q ∣ T ^ (2 ^ j) + 1) :
    2 ^ (j + 1) ∣ q - 1 := by
  letI : Fact q.Prime := ⟨hq⟩
  have horder := oddPrime_divisor_has_private_order hq hqodd hdiv
  rw [← horder]
  apply ZMod.orderOf_dvd_card_sub_one
  intro hzero
  have hpowzero : (T : ZMod q) ^ (2 ^ j) = 0 := by rw [hzero]; simp
  have hminus : (T : ZMod q) ^ (2 ^ j) = -1 := by
    have hmod : T ^ (2 ^ j) + 1 ≡ 0 [MOD q] :=
      Nat.modEq_zero_iff_dvd.mpr hdiv
    have hz : ((T ^ (2 ^ j) + 1 : ℕ) : ZMod q) = 0 := by
      simpa only [Nat.cast_zero] using
        (ZMod.natCast_eq_natCast_iff (T ^ (2 ^ j) + 1) 0 q).2 hmod
    push_cast at hz
    exact eq_neg_of_add_eq_zero_left hz
  have : (-1 : ZMod q) = 0 := hminus.symm.trans hpowzero
  exact one_ne_zero (neg_eq_zero.mp this)

/-- An odd prime cannot occur at two different dyadic levels for the same base. -/
theorem oddPrime_divisor_private
    {T q i j : ℕ} (hq : q.Prime) (hqodd : q ≠ 2)
    (hi : q ∣ T ^ (2 ^ i) + 1) (hj : q ∣ T ^ (2 ^ j) + 1) :
    i = j := by
  have hoi := oddPrime_divisor_has_private_order hq hqodd hi
  have hoj := oddPrime_divisor_has_private_order hq hqodd hj
  have hpows : 2 ^ (i + 1) = 2 ^ (j + 1) := hoi.symm.trans hoj
  have hexp : i + 1 = j + 1 := Nat.pow_right_injective (by norm_num) hpows
  omega

end LeanProofs.TwoBaseIntegerExponent.DyadicPrivateSupport
