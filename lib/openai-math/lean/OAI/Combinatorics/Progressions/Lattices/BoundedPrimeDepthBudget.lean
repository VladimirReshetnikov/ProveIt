import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def boundedPrimes (Q : ℕ) : Finset ℕ := (Finset.range (Q + 1)).filter Nat.Prime

abbrev BoundedPrime (Q : ℕ) := {p // p ∈ boundedPrimes Q}

def boundedPrime (Q : ℕ) (p : BoundedPrime Q) : ℕ := p.val

def boundedPrimeExponent (Q : ℕ) (p : BoundedPrime Q) : ℕ := Nat.log p.val Q

def boundedPrimePower (Q : ℕ) (p : BoundedPrime Q) : ℕ := p.val ^ boundedPrimeExponent Q p

theorem mem_boundedPrimes (Q p : ℕ) : p ∈ boundedPrimes Q ↔ p.Prime ∧ p ≤ Q := by
  simp only [boundedPrimes, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, and_comm]

theorem boundedPrime_prime (Q : ℕ) (p : BoundedPrime Q) : (boundedPrime Q p).Prime :=
  ((mem_boundedPrimes Q p.val).mp p.property).1

theorem boundedPrime_le (Q : ℕ) (p : BoundedPrime Q) : boundedPrime Q p ≤ Q :=
  ((mem_boundedPrimes Q p.val).mp p.property).2

theorem boundedPrime_injective (Q : ℕ) : Function.Injective (boundedPrime Q) := Subtype.val_injective

theorem boundedPrimeExponent_pos (Q : ℕ) (p : BoundedPrime Q) : 0 < boundedPrimeExponent Q p :=
  Nat.log_pos (boundedPrime_prime Q p).one_lt (boundedPrime_le Q p)

theorem boundedPrimePower_pos (Q : ℕ) (p : BoundedPrime Q) : 0 < boundedPrimePower Q p :=
  pow_pos (boundedPrime_prime Q p).pos _

instance boundedPrimePower_neZero (Q : ℕ) (p : BoundedPrime Q) : NeZero (boundedPrimePower Q p) :=
  ⟨(boundedPrimePower_pos Q p).ne'⟩

theorem boundedPrimePower_le (Q : ℕ) (p : BoundedPrime Q) : boundedPrimePower Q p ≤ Q := by
  have hQ : 0 < Q := (boundedPrime_prime Q p).pos.trans_le (boundedPrime_le Q p)
  exact Nat.pow_log_le_self p.val hQ.ne'

theorem boundedPrimePower_maximal (Q : ℕ) (p : BoundedPrime Q) :
    Q < p.val ^ (boundedPrimeExponent Q p + 1) :=
  Nat.lt_pow_succ_log_self (boundedPrime_prime Q p).one_lt Q

theorem boundedPrime_card_le (Q : ℕ) : Fintype.card (BoundedPrime Q) ≤ Q := by
  have hsub : boundedPrimes Q ⊆ (Finset.range (Q + 1)).erase 0 := by
    intro p hp
    have h := (mem_boundedPrimes Q p).mp hp
    exact Finset.mem_erase.mpr ⟨h.1.ne_zero, Finset.mem_range.mpr (by omega)⟩
  calc
    _ = (boundedPrimes Q).card := Fintype.card_coe _
    _ ≤ ((Finset.range (Q + 1)).erase 0).card := Finset.card_le_card hsub
    _ = Q := by simp

theorem boundedPrimePower_pairwise (Q : ℕ) :
    Pairwise (fun p r : BoundedPrime Q => (boundedPrimePower Q p).Coprime (boundedPrimePower Q r)) := by
  intro p r hpr
  apply Nat.Coprime.pow
  exact (Nat.coprime_primes (boundedPrime_prime Q p) (boundedPrime_prime Q r)).mpr
    (fun h => hpr (Subtype.ext h))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def boundedPrimeProduct (Q : ℕ) : ℕ := ∏ p : BoundedPrime Q, boundedPrimePower Q p

theorem boundedPrimeProduct_pos (Q : ℕ) : 0 < boundedPrimeProduct Q :=
  Finset.prod_pos (fun p _ => boundedPrimePower_pos Q p)

theorem boundedPrimeProduct_captures {Q m : ℕ} (hm : 0 < m) (hmQ : m ≤ Q) :
    m ∣ boundedPrimeProduct Q := by
  have hQ : Q ≠ 0 := (hm.trans_le hmQ).ne'
  have hsub : m.primeFactors ⊆ boundedPrimes Q := by
    intro p hp
    have h := Nat.mem_primeFactors.mp hp
    exact (mem_boundedPrimes Q p).mpr ⟨h.1, (Nat.le_of_dvd hm h.2.1).trans hmQ⟩
  have hpow (p : ℕ) (hp : p ∈ m.primeFactors) :
      p ^ m.factorization p ∣ p ^ Nat.log p Q := by
    have hprime := (Nat.mem_primeFactors.mp hp).1
    apply Nat.pow_dvd_pow
    apply (Nat.le_log_iff_pow_le hprime.one_lt hQ).mpr
    exact (Nat.le_of_dvd hm (Nat.ordProj_dvd m p)).trans hmQ
  have hsmall : m ∣ ∏ p ∈ m.primeFactors, p ^ Nat.log p Q := by
    nth_rw 1 [Nat.prod_primeFactors_pow_factorization hm.ne']
    exact Finset.prod_dvd_prod_of_dvd _ _ hpow
  have hlarge := Finset.prod_dvd_prod_of_subset m.primeFactors (boundedPrimes Q)
    (fun p => p ^ Nat.log p Q) hsub
  have h := hsmall.trans hlarge
  have he : boundedPrimeProduct Q = ∏ p ∈ boundedPrimes Q, p ^ Nat.log p Q :=
    Finset.prod_coe_sort (boundedPrimes Q) (fun p => p ^ Nat.log p Q)
  rwa [he]

end Erdos3

end

section

namespace Erdos3

theorem natLog_ceil_exp_le_linear {p : ℕ} (hp : 2 ≤ p)
    {B : ℝ} (hB : 0 ≤ B) :
    (Nat.log p ⌈Real.exp B⌉₊ : ℝ) ≤ 2 * B + 2 := by
  let Q : ℕ := ⌈Real.exp B⌉₊
  let n : ℕ := Nat.log p Q
  have hQ : 0 < Q := Nat.ceil_pos.mpr (Real.exp_pos B)
  have hpowNat : 2 ^ n ≤ Q :=
    (Nat.pow_le_pow_left hp n).trans (Nat.pow_log_le_self p hQ.ne')
  have hpow : (2 : ℝ) ^ n ≤ Q := by exact_mod_cast hpowNat
  have hceil : (Q : ℝ) ≤ 2 * Real.exp B := by
    have hc := Nat.ceil_lt_add_one (Real.exp_pos B).le
    have he : 1 ≤ Real.exp B := Real.one_le_exp_iff.mpr hB
    dsimp [Q]
    linarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ n)
    (hpow.trans hceil)
  rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (Real.exp_ne_zero B), Real.log_exp] at hlog
  have hhalf : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hone : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  dsimp [n, Q] at hlog hn ⊢
  nlinarith

theorem prime_natLog_tested_depth_le {p : ℕ} (hp : p.Prime)
    {Ptest : ℝ} (hPtest : 0 ≤ Ptest) :
    (Nat.log p ⌈Real.exp (2 * Ptest)⌉₊ : ℝ) ≤ 4 * Ptest + 2 := by
  have h := natLog_ceil_exp_le_linear hp.two_le
    (B := 2 * Ptest) (mul_nonneg (by norm_num) hPtest)
  nlinarith

theorem exists_testedPrimeDepth {Ptest : ℝ} (hPtest : 0 ≤ Ptest) :
    ∃ depth : ℕ, (depth : ℝ) ≤ 4 * Ptest + 2 ∧
      ∀ p : ℕ, p.Prime → Nat.log p ⌈Real.exp (2 * Ptest)⌉₊ ≤ depth := by
  have hnonneg : 0 ≤ 4 * Ptest + 2 := by positivity
  refine ⟨⌊4 * Ptest + 2⌋₊, Nat.floor_le hnonneg, ?_⟩
  intro p hp
  exact Nat.le_floor (prime_natLog_tested_depth_le hp hPtest)

end Erdos3

end

end OAI
