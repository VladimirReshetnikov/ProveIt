import ExponentialIdentities.TwoBaseIntegerExponent
import Mathlib.Data.Rat.Lemmas

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-- If a positive power of a positive rational has its denominator canceled by a power of
three, then the reduced denominator of the rational is itself a power of three. -/
theorem rat_den_eq_three_pow_of_pow_mul_three_pow_integer
    {q : ℚ} (hq : 0 < q) {i k : ℕ} (hk : 0 < k)
    (hint : ∃ z : ℤ, (z : ℚ) = (3 : ℚ) ^ i * q ^ k) :
    ∃ a : ℕ, a ≤ i ∧ q.den = 3 ^ a := by
  obtain ⟨z, hz⟩ := hint
  have hzPosQ : (0 : ℚ) < (z : ℚ) := by
    rw [hz]
    positivity
  have hzPos : (0 : ℤ) < z := by exact_mod_cast hzPosQ
  obtain ⟨z₀, rfl⟩ := Int.eq_ofNat_of_zero_le hzPos.le
  let c : ℕ := q.num.natAbs
  have hnumPos : 0 < q.num := Rat.num_pos.mpr hq
  have hcPos : 0 < c := by
    dsimp only [c]
    exact Int.natAbs_pos.mpr hnumPos.ne'
  have hcNum : (c : ℤ) = q.num := by
    dsimp only [c]
    exact Int.natAbs_of_nonneg hnumPos.le
  have hz' : (z₀ : ℚ) = (3 : ℚ) ^ i * q ^ k := by
    exact_mod_cast hz
  have hzR : (z₀ : ℝ) = (3 : ℝ) ^ i * (q : ℝ) ^ k := by
    exact_mod_cast hz'
  have hqR : (q : ℝ) = (c : ℝ) / (q.den : ℝ) := by
    rw [Rat.cast_def, ← hcNum]
    norm_num
  have hclearR :
      (z₀ : ℝ) * (q.den : ℝ) ^ k =
        (3 : ℝ) ^ i * (c : ℝ) ^ k := by
    rw [hzR, hqR, div_pow]
    field_simp
  have hclearN : z₀ * q.den ^ k = 3 ^ i * c ^ k := by
    exact_mod_cast hclearR
  have hdvdProduct : q.den ^ k ∣ 3 ^ i * c ^ k := by
    refine ⟨z₀, ?_⟩
    rw [← hclearN, mul_comm]
  have hcop : (q.den ^ k).Coprime (c ^ k) := by
    exact (Nat.Coprime.pow k k (by simpa only [c] using q.reduced)).symm
  have hdvdPow : q.den ^ k ∣ 3 ^ i :=
    hcop.dvd_of_dvd_mul_right hdvdProduct
  have hdenDvd : q.den ∣ 3 ^ i :=
    (dvd_pow_self q.den hk.ne').trans hdvdPow
  exact (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdenDvd

/-- A positive rational whose positive power has denominator canceled by a power of three
can be written with a power-of-three denominator.  The numerator is prime to three whenever
the denominator is nontrivial. -/
theorem exists_three_pow_denominator_of_pow_mul_three_pow_integer
    {q : ℚ} (hq : 0 < q) {i k : ℕ} (hk : 0 < k)
    (hint : ∃ z : ℤ, (z : ℚ) = (3 : ℚ) ^ i * q ^ k) :
    ∃ a c : ℕ, 0 < c ∧ (a = 0 ∨ ¬ 3 ∣ c) ∧
      q = (c : ℚ) / (3 : ℚ) ^ a := by
  obtain ⟨a, _haLe, hden⟩ :=
    rat_den_eq_three_pow_of_pow_mul_three_pow_integer hq hk hint
  let c : ℕ := q.num.natAbs
  have hnumPos : 0 < q.num := Rat.num_pos.mpr hq
  have hcPos : 0 < c := by
    dsimp only [c]
    exact Int.natAbs_pos.mpr hnumPos.ne'
  have hcNum : (c : ℤ) = q.num := by
    dsimp only [c]
    exact Int.natAbs_of_nonneg hnumPos.le
  refine ⟨a, c, hcPos, ?_, ?_⟩
  · rcases a.eq_zero_or_pos with ha | ha
    · exact Or.inl ha
    · refine Or.inr ?_
      intro h3c
      apply (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 3) h3c ?_) q.reduced
      rw [hden]
      exact dvd_pow_self 3 ha.ne'
  · apply Rat.cast_injective (α := ℝ)
    push_cast
    rw [Rat.cast_def, ← hcNum, hden]
    norm_num

/-- Real-cast form of the normalized denominator calculation used for a rational power
`E ^ d`.  The condition on `c` is necessarily conditional when the denominator is `1`. -/
theorem exists_three_pow_denominator_of_rational_power
    {E : ℝ} (hE : 0 < E) {d i k : ℕ} (_hd : 0 < d) (hk : 0 < k)
    (hq : E ^ d ∈ Set.range ((↑) : ℚ → ℝ))
    (hint : (3 : ℝ) ^ i * (E ^ d) ^ k ∈ Set.range ((↑) : ℤ → ℝ)) :
    ∃ a c : ℕ, 0 < c ∧ (a = 0 ∨ ¬ 3 ∣ c) ∧
      E ^ d = (c : ℝ) / (3 : ℝ) ^ a := by
  obtain ⟨q, hqE⟩ := hq
  have hqPosR : (0 : ℝ) < (q : ℝ) := by
    rw [hqE]
    positivity
  have hqPos : (0 : ℚ) < q := by exact_mod_cast hqPosR
  obtain ⟨z, hz⟩ := hint
  have hzQ : (z : ℚ) = (3 : ℚ) ^ i * q ^ k := by
    rw [← hqE] at hz
    exact_mod_cast hz
  obtain ⟨a, c, hc, hc3, hqNorm⟩ :=
    exists_three_pow_denominator_of_pow_mul_three_pow_integer hqPos hk ⟨z, hzQ⟩
  refine ⟨a, c, hc, hc3, ?_⟩
  calc
    E ^ d = (q : ℝ) := hqE.symm
    _ = (c : ℝ) / (3 : ℝ) ^ a := by
      have hcast := congrArg (fun r : ℚ ↦ (r : ℝ)) hqNorm
      push_cast at hcast
      exact hcast

end

end LeanProofs.TwoBaseIntegerExponent
