import ExponentialIdentities.TwoBaseIntegerExponent.FiniteCheck256

/-!
# Arithmetic rigidity of a hypothetical two-base counterexample

This file records exact descent operations on a solution.  If the two integral outputs have
the simultaneous shapes

`2 ^ r * a ^ k = 2 ^ x` and `3 ^ r * b ^ k = 3 ^ x`,

then `(x - r) / k` is another solution.  Combining this identity with the verified zero-free
region below `8` gives the unconditional restriction `r + 8 * k ≤ x` on every hypothetical
nonintegral solution.  Specializations treat common perfect powers and the matched base-adic
depth of the two outputs.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

private theorem two_three_natural_monomial_injective :
    Function.Injective (fun u : ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h₂ := congrArg (fun n : ℕ ↦ n.factorization 2) h
  have ha : a = c := by
    simpa [Nat.factorization_mul,
      Nat.Prime.factorization_pow (by decide : Nat.Prime 2),
      Nat.Prime.factorization_pow (by decide : Nat.Prime 3)] using h₂
  have h₃ := congrArg (fun n : ℕ ↦ n.factorization 3) h
  have hb : b = d := by
    simpa [Nat.factorization_mul,
      Nat.Prime.factorization_pow (by decide : Nat.Prime 2),
      Nat.Prime.factorization_pow (by decide : Nat.Prime 3)] using h₃
  exact Prod.ext ha hb

/-- For any nonzero exponent, the integral outputs `m = 2 ^ x` and `n = 3 ^ x` have
distinct natural monomials. -/
theorem output_monomial_injective
    {x : ℝ} (hx : x ≠ 0) {m n : ℕ}
    (hm : (m : ℝ) = (2 : ℝ) ^ x)
    (hn : (n : ℝ) = (3 : ℝ) ^ x) :
    Function.Injective (fun u : ℕ × ℕ ↦ m ^ u.1 * n ^ u.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  apply two_three_natural_monomial_injective
  have hrepr (i j : ℕ) :
      (((m ^ i * n ^ j : ℕ) : ℝ)) =
        (((2 ^ i * 3 ^ j : ℕ) : ℝ)) ^ x := by
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) x i,
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) x j]
    rw [← hm, ← hn]
  have hpow :
      (((2 ^ a * 3 ^ b : ℕ) : ℝ)) ^ x =
        (((2 ^ c * 3 ^ d : ℕ) : ℝ)) ^ x := by
    rw [← hrepr a b, ← hrepr c d]
    exact_mod_cast h
  have hbase :
      (((2 ^ a * 3 ^ b : ℕ) : ℝ)) =
        (((2 ^ c * 3 ^ d : ℕ) : ℝ)) :=
    (Real.rpow_left_inj (by positivity) (by positivity) hx).mp hpow
  exact_mod_cast hbase

/-- If both integral outputs are `k`-th powers, dividing the exponent by `k` produces
another two-base solution. -/
theorem divided_exponent_integral_powers_of_common_perfect_power
    {x : ℝ} {a b k : ℕ} (hk : 0 < k)
    (hm : ((a ^ k : ℕ) : ℝ) = (2 : ℝ) ^ x)
    (hn : ((b ^ k : ℕ) : ℝ) = (3 : ℝ) ^ x) :
    (∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ (x / k)) ∧
      ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ (x / k) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  constructor
  · refine ⟨(a : ℤ), ?_⟩
    have hpow : ((2 : ℝ) ^ (x / k)) ^ k = (a : ℝ) ^ k := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      rw [div_mul_cancel₀ x hkR]
      simpa using hm.symm
    exact ((pow_left_inj₀ (Real.rpow_nonneg (by norm_num) _)
      (Nat.cast_nonneg a) hk.ne').mp hpow).symm
  · refine ⟨(b : ℤ), ?_⟩
    have hpow : ((3 : ℝ) ^ (x / k)) ^ k = (b : ℝ) ^ k := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
      rw [div_mul_cancel₀ x hkR]
      simpa using hn.symm
    exact ((pow_left_inj₀ (Real.rpow_nonneg (by norm_num) _)
      (Nat.cast_nonneg b) hk.ne').mp hpow).symm

/-- A hypothetical nonintegral solution whose two outputs are simultaneously `k`-th powers
must satisfy `8 * k ≤ x`. -/
theorem eight_mul_le_of_common_perfect_power_outputs
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    {a b k : ℕ} (hk : 0 < k)
    (hm : ((a ^ k : ℕ) : ℝ) = (2 : ℝ) ^ x)
    (hn : ((b ^ k : ℕ) : ℝ) = (3 : ℝ) ^ x) :
    (8 : ℝ) * k ≤ x := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hy_not_integer : x / (k : ℝ) ∉ Set.range ((↑) : ℤ → ℝ) := by
    rintro ⟨z, hz⟩
    apply hx
    refine ⟨(k : ℤ) * z, ?_⟩
    push_cast
    rw [hz]
    field_simp
  obtain ⟨h₂, h₃⟩ :=
    divided_exponent_integral_powers_of_common_perfect_power hk hm hn
  have h8 := eight_le_of_not_integer_of_two_three_rpow_integer
    h₂ h₃ hy_not_integer
  exact (le_div_iff₀ hkR).mp (by simpa [mul_comm] using h8)

/-- Unified affine descent.  If the two outputs have the forms `2 ^ r * a ^ k` and
`3 ^ r * b ^ k`, then `(x - r) / k` is another two-base solution. -/
theorem affine_descent_integral_powers
    {x : ℝ} {a b r k : ℕ} (hk : 0 < k)
    (hm : ((2 ^ r * a ^ k : ℕ) : ℝ) = (2 : ℝ) ^ x)
    (hn : ((3 ^ r * b ^ k : ℕ) : ℝ) = (3 : ℝ) ^ x) :
    (∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ ((x - r) / k)) ∧
      ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ ((x - r) / k) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  constructor
  · refine ⟨(a : ℤ), ?_⟩
    have hpow : ((2 : ℝ) ^ ((x - r) / k)) ^ k = (a : ℝ) ^ k := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      rw [div_mul_cancel₀ (x - r) hkR]
      rw [Real.rpow_sub_natCast (by norm_num : (2 : ℝ) ≠ 0), ← hm]
      push_cast
      field_simp
    exact ((pow_left_inj₀ (Real.rpow_nonneg (by norm_num) _)
      (Nat.cast_nonneg a) hk.ne').mp hpow).symm
  · refine ⟨(b : ℤ), ?_⟩
    have hpow : ((3 : ℝ) ^ ((x - r) / k)) ^ k = (b : ℝ) ^ k := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
      rw [div_mul_cancel₀ (x - r) hkR]
      rw [Real.rpow_sub_natCast (by norm_num : (3 : ℝ) ≠ 0), ← hn]
      push_cast
      field_simp
    exact ((pow_left_inj₀ (Real.rpow_nonneg (by norm_num) _)
      (Nat.cast_nonneg b) hk.ne').mp hpow).symm

/-- Quantitative affine rigidity: the verified zero-free interval `[0, 8)` propagates through
every simultaneous affine decomposition of the outputs. -/
theorem base_depth_add_eight_mul_degree_le
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    {a b r k : ℕ} (hk : 0 < k)
    (hm : ((2 ^ r * a ^ k : ℕ) : ℝ) = (2 : ℝ) ^ x)
    (hn : ((3 ^ r * b ^ k : ℕ) : ℝ) = (3 : ℝ) ^ x) :
    (r : ℝ) + 8 * k ≤ x := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hy_not_integer :
      (x - (r : ℝ)) / (k : ℝ) ∉ Set.range ((↑) : ℤ → ℝ) := by
    rintro ⟨z, hz⟩
    apply hx
    refine ⟨(r : ℤ) + (k : ℤ) * z, ?_⟩
    push_cast
    rw [hz]
    field_simp
    ring
  obtain ⟨h₂, h₃⟩ := affine_descent_integral_powers hk hm hn
  have h8 := eight_le_of_not_integer_of_two_three_rpow_integer
    h₂ h₃ hy_not_integer
  have hmul : (8 : ℝ) * k ≤ x - r := (le_div_iff₀ hkR).mp h8
  linarith

/-- Subtracting a common matched base-adic depth preserves a two-base solution. -/
theorem shifted_integral_powers_of_common_divisibility
    {x : ℝ} {m n r : ℕ}
    (hm : (m : ℝ) = (2 : ℝ) ^ x)
    (hn : (n : ℝ) = (3 : ℝ) ^ x)
    (hdiv₂ : 2 ^ r ∣ m) (hdiv₃ : 3 ^ r ∣ n) :
    (∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ (x - r)) ∧
      ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ (x - r) := by
  obtain ⟨a, rfl⟩ := hdiv₂
  obtain ⟨b, rfl⟩ := hdiv₃
  constructor
  · refine ⟨(a : ℤ), ?_⟩
    rw [Real.rpow_sub_natCast (by norm_num : (2 : ℝ) ≠ 0), ← hm]
    push_cast
    field_simp
  · refine ⟨(b : ℤ), ?_⟩
    rw [Real.rpow_sub_natCast (by norm_num : (3 : ℝ) ≠ 0), ← hn]
    push_cast
    field_simp

/-- A nonintegral solution cannot have a common matched base-adic depth extending to within
eight units of its exponent. -/
theorem common_base_adic_depth_add_eight_le
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    {m n r : ℕ}
    (hm : (m : ℝ) = (2 : ℝ) ^ x)
    (hn : (n : ℝ) = (3 : ℝ) ^ x)
    (hdiv₂ : 2 ^ r ∣ m) (hdiv₃ : 3 ^ r ∣ n) :
    (r : ℝ) + 8 ≤ x := by
  have hy_not_integer : x - (r : ℝ) ∉ Set.range ((↑) : ℤ → ℝ) := by
    rintro ⟨z, hz⟩
    apply hx
    refine ⟨z + (r : ℤ), ?_⟩
    push_cast
    linarith
  obtain ⟨h₂, h₃⟩ :=
    shifted_integral_powers_of_common_divisibility hm hn hdiv₂ hdiv₃
  have h8 := eight_le_of_not_integer_of_two_three_rpow_integer
    h₂ h₃ hy_not_integer
  linarith

/-- Valuation form: the smaller of the `2`-adic depth of `m = 2 ^ x` and the `3`-adic depth
of `n = 3 ^ x` lies at least eight below a hypothetical nonintegral exponent. -/
theorem min_output_base_factorization_add_eight_le
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    {m n : ℕ}
    (hm : (m : ℝ) = (2 : ℝ) ^ x)
    (hn : (n : ℝ) = (3 : ℝ) ^ x) :
    ((min (m.factorization 2) (n.factorization 3) : ℕ) : ℝ) + 8 ≤ x := by
  have hm0 : m ≠ 0 := by
    intro hmzero
    have : (0 : ℝ) < (m : ℝ) := hm.trans_gt (Real.rpow_pos_of_pos (by norm_num) x)
    simp [hmzero] at this
  have hn0 : n ≠ 0 := by
    intro hnzero
    have : (0 : ℝ) < (n : ℝ) := hn.trans_gt (Real.rpow_pos_of_pos (by norm_num) x)
    simp [hnzero] at this
  apply common_base_adic_depth_add_eight_le hx hm hn
  · exact (Nat.prime_two.pow_dvd_iff_le_factorization hm0).2 (min_le_left _ _)
  · exact ((by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization hn0).2
      (min_le_right _ _)

end LeanProofs.TwoBaseIntegerExponent
