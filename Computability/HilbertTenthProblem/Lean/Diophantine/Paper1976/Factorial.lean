import Diophantine.Paper1976.Ineq

/-!
# JSWW 1976, Lemma 2.10: the factorial through a binomial remainder

> **Lemma 2.10.** For any positive integer `k`, if `(2k)^k ≤ n` and `n^k < p` then
> `k! < (n+1)^k p^k / r((p+1)^n, p^(k+1)) < k! + 1`.

Here `r(y, x)` is the remainder of `y` on division by `x`.  The statement is
formalized without division: with `R = (p+1)^n mod p^(k+1)`,
`0 < R`, `k! · R < (n+1)^k p^k` and `(n+1)^k p^k < (k!+1) · R`.
The proof follows the article: `R` is the partial binomial sum
`S = Σ_{i ≤ k} C(n,i) p^i`, bounded above by the geometric sum (i), then (ii) and
(iii)/(iv) (the latter from `Ineq.lean`).
-/

namespace JSWW1976

open Finset

/-- The partial binomial sum `Σ_{i ≤ k} C(n,i) p^i`. -/
def partialSum (n p k : ℕ) : ℕ := ∑ i ∈ range (k + 1), n.choose i * p ^ i

/-- `(p+1)^n = partialSum n p k + p^(k+1) · T` for some `T`, when `k < n`. -/
theorem pow_eq_partialSum_add {n p k : ℕ} (hk : k < n) :
    ∃ T, (p + 1) ^ n = partialSum n p k + p ^ (k + 1) * T := by
  have h := add_pow p 1 n
  simp only [one_pow, mul_one, Nat.cast_id] at h
  -- (p+1)^n = Σ_{m < n+1} p^m * C(n,m)
  have hsplit : ∑ m ∈ range (n + 1), p ^ m * n.choose m =
      ∑ m ∈ range (k + 1), p ^ m * n.choose m + ∑ m ∈ Ico (k + 1) (n + 1), p ^ m * n.choose m := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)).symm
  have hdvd : p ^ (k + 1) ∣ ∑ m ∈ Ico (k + 1) (n + 1), p ^ m * n.choose m := by
    apply Finset.dvd_sum
    intro m hm
    simp only [Finset.mem_Ico] at hm
    exact Dvd.dvd.mul_right (pow_dvd_pow p hm.1) _
  obtain ⟨T, hT⟩ := hdvd
  refine ⟨T, ?_⟩
  rw [h, hsplit, hT, partialSum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _; ring

/-- `C(n, i) ≤ n^i`. -/
theorem choose_le_pow' (n i : ℕ) : n.choose i ≤ n ^ i := by
  have h1 : i.factorial * n.choose i = n.descFactorial i := (Nat.descFactorial_eq_factorial_mul_choose n i).symm
  have h2 : n.descFactorial i ≤ n ^ i := Nat.descFactorial_le_pow n i
  have h3 : n.choose i ≤ i.factorial * n.choose i :=
    Nat.le_mul_of_pos_left _ (Nat.factorial_pos i)
  omega

/-- (i): the partial sum is below `p^(k+1)` when `1 ≤ n` and `n^k < p`. -/
theorem partialSum_lt {n p k : ℕ} (hn : 1 ≤ n) (hp : n ^ k < p) :
    partialSum n p k < p ^ (k + 1) := by
  have hp1 : 1 ≤ p := by have := Nat.one_le_pow k n hn; omega
  -- S ≤ Σ (np)^i =: G
  have hG : partialSum n p k ≤ ∑ i ∈ range (k + 1), (n * p) ^ i := by
    unfold partialSum
    apply Finset.sum_le_sum
    intro i _
    rw [mul_pow]
    exact Nat.mul_le_mul_right _ (choose_le_pow' n i)
  -- G (np - 1) = (np)^(k+1) - 1 in ℤ, and (np)^(k+1) - 1 < (np - 1) p^(k+1)
  have hnp : 2 ≤ n * p := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp at hp; nlinarith
    · have : n ≤ n ^ k := Nat.le_self_pow hk0.ne' n
      nlinarith
  have hgeom : ((∑ i ∈ range (k + 1), (n * p) ^ i : ℕ) : ℤ) * ((n * p : ℤ) - 1) = (n * p : ℤ) ^ (k + 1) - 1 := by
    have := geom_sum_mul (x := ((n * p : ℕ) : ℤ)) (k + 1)
    push_cast at this ⊢
    exact this
  have hlt : ((n * p : ℤ) ^ (k + 1) - 1) < ((n * p : ℤ) - 1) * (p : ℤ) ^ (k + 1) := by
    have hpk : ((n : ℤ) ^ k + 1) ≤ p := by exact_mod_cast hp
    have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
    have hp' : (1 : ℤ) ≤ p := by exact_mod_cast hp1
    have hpow : (0 : ℤ) < (p : ℤ) ^ (k + 1) := by positivity
    have key : (n * p : ℤ) ^ (k + 1) = (n : ℤ) ^ k * n * p ^ (k + 1) := by ring
    have h1 : (n : ℤ) ^ k * n * p ^ (k + 1) ≤ ((p : ℤ) - 1) * n * p ^ (k + 1) := by
      have : (n : ℤ) ^ k ≤ p - 1 := by linarith
      have hnp' : (0 : ℤ) ≤ n * p ^ (k + 1) := by positivity
      nlinarith
    nlinarith
  have hG' : ((∑ i ∈ range (k + 1), (n * p) ^ i : ℕ) : ℤ) < (p : ℤ) ^ (k + 1) := by
    have hpos : (0 : ℤ) < (n * p : ℤ) - 1 := by
      have : (2 : ℤ) ≤ n * p := by exact_mod_cast hnp
      linarith
    have hmul : ((∑ i ∈ range (k + 1), (n * p) ^ i : ℕ) : ℤ) * ((n * p : ℤ) - 1)
        < (p : ℤ) ^ (k + 1) * ((n * p : ℤ) - 1) := by
      rw [hgeom]; linarith
    exact lt_of_mul_lt_mul_right hmul hpos.le
  have : (∑ i ∈ range (k + 1), (n * p) ^ i) < p ^ (k + 1) := by exact_mod_cast hG'
  omega

/-- `(n+1)^k ≥ n^k + k n^(k-1)` for `k ≥ 1`. -/
theorem succ_pow_ge {n m : ℕ} : n ^ (m + 1) + (m + 1) * n ^ m ≤ (n + 1) ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc n ^ (m + 2) + (m + 2) * n ^ (m + 1)
        ≤ (n + 1) * (n ^ (m + 1) + (m + 1) * n ^ m) := by
          have e : (n + 1) * (n ^ (m + 1) + (m + 1) * n ^ m)
              = n ^ (m + 2) + (m + 2) * n ^ (m + 1) + (m + 1) * n ^ m := by ring
          rw [e]; omega
      _ ≤ (n + 1) * (n + 1) ^ (m + 1) := Nat.mul_le_mul_left _ ih
      _ = (n + 1) ^ (m + 2) := by ring

/-- (ii): `k! · partialSum < (n+1)^k p^k` under the hypotheses of Lemma 2.10. -/
theorem factorial_mul_partialSum_lt {n p k : ℕ} (hk : 1 ≤ k) (hn : (2 * k) ^ k ≤ n)
    (hp : n ^ k < p) : k.factorial * partialSum n p k < (n + 1) ^ k * p ^ k := by
  have hn1 : 1 ≤ n := by
    have : 1 ≤ (2 * k) ^ k := Nat.one_le_pow _ _ (by omega)
    omega
  have hkfac : k.factorial < p := by
    -- k! ≤ k^k ≤ (2k)^k ≤ n ≤ n^k < p
    have h1 : k.factorial ≤ k ^ k := Nat.factorial_le_pow k
    have h2 : k ^ k ≤ (2 * k) ^ k := Nat.pow_le_pow_left (by omega) _
    have h3 : n ≤ n ^ k := Nat.le_self_pow (by omega) n
    omega
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  -- split the sum: Σ_{i ≤ m} + the top term
  have hsplit : partialSum n p (m + 1) = (∑ i ∈ range (m + 1), n.choose i * p ^ i) + n.choose (m + 1) * p ^ (m + 1) := by
    unfold partialSum; rw [Finset.sum_range_succ]
  -- each low term is ≤ (np)^m
  have hnp1 : 1 ≤ n * p := Nat.mul_pos hn1 (by omega)
  have hlow : (∑ i ∈ range (m + 1), n.choose i * p ^ i) ≤ (m + 1) * (n * p) ^ m := by
    calc (∑ i ∈ range (m + 1), n.choose i * p ^ i) ≤ ∑ i ∈ range (m + 1), (n * p) ^ m := by
          apply Finset.sum_le_sum
          intro i hi
          simp only [Finset.mem_range] at hi
          calc n.choose i * p ^ i ≤ n ^ i * p ^ i := Nat.mul_le_mul_right _ (choose_le_pow' n i)
            _ = (n * p) ^ i := by rw [mul_pow]
            _ ≤ (n * p) ^ m := Nat.pow_le_pow_right hnp1 (by omega)
      _ = (m + 1) * (n * p) ^ m := by simp
  have htop : (m + 1).factorial * n.choose (m + 1) ≤ n ^ (m + 1) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]; exact Nat.descFactorial_le_pow n (m + 1)
  have hbin := succ_pow_ge (n := n) (m := m)
  -- assemble
  have hfac_pos : 0 < (m + 1).factorial := Nat.factorial_pos _
  calc (m + 1).factorial * partialSum n p (m + 1)
      = (m + 1).factorial * (∑ i ∈ range (m + 1), n.choose i * p ^ i)
        + (m + 1).factorial * n.choose (m + 1) * p ^ (m + 1) := by rw [hsplit]; ring
    _ ≤ (m + 1).factorial * ((m + 1) * (n * p) ^ m) + n ^ (m + 1) * p ^ (m + 1) := by
        gcongr
    _ < (m + 1) * n ^ m * p ^ m * p + n ^ (m + 1) * p ^ (m + 1) := by
        have : (m + 1).factorial * ((m + 1) * (n * p) ^ m) < (m + 1) * n ^ m * p ^ m * p := by
          rw [mul_pow]
          have hpos : 0 < (m + 1) * n ^ m * p ^ m := by
            have : 0 < p := by omega
            positivity
          calc (m + 1).factorial * ((m + 1) * (n ^ m * p ^ m)) = (m + 1) * n ^ m * p ^ m * (m + 1).factorial := by ring
            _ < (m + 1) * n ^ m * p ^ m * p := Nat.mul_lt_mul_of_pos_left hkfac hpos
        omega
    _ = ((m + 1) * n ^ m + n ^ (m + 1)) * p ^ (m + 1) := by ring
    _ ≤ (n + 1) ^ (m + 1) * p ^ (m + 1) := by
        apply Nat.mul_le_mul_right
        linarith [hbin]

/-- Lemma 2.10, without division: with `R = (p+1)^n mod p^(k+1)`,
`0 < R`, `k! R < (n+1)^k p^k` and `(n+1)^k p^k < (k!+1) R`. -/
theorem lemma_2_10 {k n p : ℕ} (hk : 1 ≤ k) (hn : (2 * k) ^ k ≤ n) (hp : n ^ k < p) :
    0 < (p + 1) ^ n % p ^ (k + 1) ∧
    k.factorial * ((p + 1) ^ n % p ^ (k + 1)) < (n + 1) ^ k * p ^ k ∧
    (n + 1) ^ k * p ^ k < (k.factorial + 1) * ((p + 1) ^ n % p ^ (k + 1)) := by
  have hn1 : 1 ≤ n := by
    have : 1 ≤ (2 * k) ^ k := Nat.one_le_pow _ _ (by omega)
    omega
  have hkn : k < n := by
    have : 2 * k ≤ (2 * k) ^ k := Nat.le_self_pow (by omega) _
    omega
  -- the remainder is the partial sum
  obtain ⟨T, hT⟩ := pow_eq_partialSum_add (p := p) hkn
  have hS : (p + 1) ^ n % p ^ (k + 1) = partialSum n p k := by
    rw [hT, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (partialSum_lt hn1 hp)]
  rw [hS]
  refine ⟨?_, factorial_mul_partialSum_lt hk hn hp, ?_⟩
  · -- the i = 0 term is 1
    unfold partialSum
    calc 0 < n.choose 0 * p ^ 0 := by simp
      _ ≤ ∑ i ∈ range (k + 1), n.choose i * p ^ i :=
        Finset.single_le_sum (f := fun i => n.choose i * p ^ i) (fun i _ => Nat.zero_le _) (by simp)
  · -- top term C(n,k) p^k ≤ S and k!(n+1)^k < (k!+1) descFactorial = (k!+1) k! C(n,k)
    have htop : n.choose k * p ^ k ≤ partialSum n p k := by
      unfold partialSum
      exact Finset.single_le_sum (f := fun i => n.choose i * p ^ i) (fun i _ => Nat.zero_le _) (by simp)
    have hiv := lemma_2_10_iv hk hn
    rw [Nat.descFactorial_eq_factorial_mul_choose] at hiv
    have hfac_pos : 0 < k.factorial := Nat.factorial_pos k
    have : k.factorial * ((n + 1) ^ k * p ^ k) < k.factorial * ((k.factorial + 1) * partialSum n p k) := by
      calc k.factorial * ((n + 1) ^ k * p ^ k) = k.factorial * (n + 1) ^ k * p ^ k := by ring
        _ < (k.factorial + 1) * (k.factorial * n.choose k) * p ^ k := by
            have hpk : 0 < p ^ k := by
              have : 0 < p := by have := Nat.one_le_pow k n hn1; omega
              positivity
            exact Nat.mul_lt_mul_of_pos_right hiv hpk
        _ = k.factorial * ((k.factorial + 1) * (n.choose k * p ^ k)) := by ring
        _ ≤ k.factorial * ((k.factorial + 1) * partialSum n p k) := by gcongr
    exact Nat.lt_of_mul_lt_mul_left this

end JSWW1976
