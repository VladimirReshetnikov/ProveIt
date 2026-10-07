import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3
open scoped Classical

theorem exists_distinct_primes_dyadic (n t : ℕ) (ht : 0 < t) :
    ∃ N : Fin n → ℕ, StrictMono N ∧
      ∀ i, (N i).Prime ∧ 2 ^ i.val * t < N i ∧ N i ≤ 2 ^ (i.val + 1) * t := by
  have hp (i : Fin n) : ∃ p : ℕ, p.Prime ∧
      2 ^ i.val * t < p ∧ p ≤ 2 ^ (i.val + 1) * t := by
    obtain ⟨p, hprime, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul
      (2 ^ i.val * t) (by positivity)
    refine ⟨p, hprime, hlo, ?_⟩
    simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hhi
  choose N hN using hp
  refine ⟨N, ?_, hN⟩
  intro i j hij
  have he : i.val + 1 ≤ j.val := by exact hij
  exact ((hN i).2.2.trans (Nat.mul_le_mul_right t
    (Nat.pow_le_pow_right (by norm_num : 0 < 2) he))).trans_lt (hN j).2.1

theorem exists_distinct_comparable_prime_sides (n L : ℕ) (hL : 0 < L)
    (hdiv : 2 ^ (n + 1) ∣ L) :
    ∃ N : Fin n → ℕ, (∀ i, (N i).Prime) ∧ Function.Injective N ∧
      ∀ i, (L : ℝ) / (2 : ℝ) ^ (n + 1) < (N i : ℝ) ∧ N i ≤ L := by
  let t := L / 2 ^ (n + 1)
  have ht : 0 < t := Nat.div_pos (Nat.le_of_dvd hL hdiv) (by positivity)
  have hprod : 2 ^ (n + 1) * t = L := Nat.mul_div_cancel' hdiv
  obtain ⟨N, hmono, hN⟩ := exists_distinct_primes_dyadic n t ht
  have htR : (L : ℝ) / (2 : ℝ) ^ (n + 1) = (t : ℝ) := by
    apply (div_eq_iff (by positivity : (2 : ℝ) ^ (n + 1) ≠ 0)).mpr
    have hh : (2 : ℝ) ^ (n + 1) * t = L := by exact_mod_cast hprod
    linarith
  refine ⟨N, fun i => (hN i).1, hmono.injective, ?_⟩
  intro i
  constructor
  · rw [htR]
    exact_mod_cast (show t < N i from
      (Nat.le_mul_of_pos_left t (by positivity : 0 < 2 ^ i.val)).trans_lt (hN i).2.1)
  · exact ((hN i).2.2.trans (Nat.mul_le_mul_right t
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : i.val + 1 ≤ n + 1)))).trans_eq hprod

theorem exists_distinct_comparable_prime_sides_above (n L : ℕ) (hL : 0 < L)
    (hdiv : 2 ^ (n + 1) ∣ L) (cutoff : ℝ)
    (hcutoff : cutoff ≤ (L : ℝ) / (2 : ℝ) ^ (n + 1)) :
    ∃ N : Fin n → ℕ, (∀ i, (N i).Prime) ∧ Function.Injective N ∧
      ∀ i, cutoff < (N i : ℝ) ∧ (L : ℝ) / (2 : ℝ) ^ (n + 1) < (N i : ℝ) ∧ N i ≤ L := by
  obtain ⟨N, hp, hi, hN⟩ := exists_distinct_comparable_prime_sides n L hL hdiv
  exact ⟨N, hp, hi, fun i => ⟨hcutoff.trans_lt (hN i).1, hN i⟩⟩

end Erdos3

end

section

namespace Erdos3
open scoped Classical

theorem exists_comparableScalarPrimeParameters (d : ℕ) {L : ℝ} (hL : 1 ≤ L) :
    ∃ parameters : Fin d → ℕ, (∀ j, (parameters j).Prime) ∧
      Function.Injective parameters ∧
      (∀ j, L ≤ (parameters j : ℝ)) ∧
      ∀ j, (parameters j : ℝ) ≤ (2 : ℝ) ^ (d + 1) * L := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hceil : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil _
  have hceilp : 0 < ⌈L⌉₊ := by exact_mod_cast hLp.trans_le hceil
  have hceilupper : (⌈L⌉₊ : ℝ) ≤ 2 * L := by
    have h := Nat.ceil_lt_add_one hLp.le
    linarith
  obtain ⟨parameters, hmono, hparam⟩ := exists_distinct_primes_dyadic d ⌈L⌉₊ hceilp
  refine ⟨parameters, fun j => (hparam j).1, hmono.injective, ?_, ?_⟩
  · intro j
    have hlower : ⌈L⌉₊ ≤ parameters j :=
      (Nat.le_mul_of_pos_left _ (by positivity : 0 < 2 ^ j.val)).trans (hparam j).2.1.le
    exact hceil.trans (by exact_mod_cast hlower)
  · intro j
    have hupper : parameters j ≤ 2 ^ d * ⌈L⌉₊ :=
      (hparam j).2.2.trans (Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : j.val + 1 ≤ d)))
    calc
      (parameters j : ℝ) ≤ (2 : ℝ) ^ d * (⌈L⌉₊ : ℝ) := by exact_mod_cast hupper
      _ ≤ (2 : ℝ) ^ d * (2 * L) :=
        mul_le_mul_of_nonneg_left hceilupper (by positivity)
      _ = (2 : ℝ) ^ (d + 1) * L := by rw [pow_succ]; ring

end Erdos3

end

end OAI
