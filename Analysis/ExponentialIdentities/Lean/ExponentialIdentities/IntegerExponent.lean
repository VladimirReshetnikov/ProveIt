import ExponentialIdentities.IntegerExponent.DeterminantBound
import ExponentialIdentities.IntegerExponent.ExponentialKernel
import ExponentialIdentities.IntegerExponent.Grid

/-!
# Integral powers at 2, 3, and 5 force an integral exponent

For a real number `x`, this file proves that if `2 ^ x`, `3 ^ x`, and `5 ^ x` are integers,
then `x` is an integer.  The irrational case is ruled out by an elementary interpolation-
determinant proof of the needed special case of the six exponentials theorem.  Once `x` is
rational, unique factorization applied to `2 ^ x` shows that its denominator is one.

The interpolation argument follows Michel Waldschmidt's square-determinant proof in
*Six exponentials Theorem -- irrationality*.
-/

open scoped BigOperators Nat

namespace LeanProofs.IntegerExponent

noncomputable section

/-- The special six-exponentials step: integral values at the three bases rule out an
irrational exponent. -/
private theorem not_irrational_of_three_prime_rpows_integer {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (h₅ : ∃ z : ℤ, (z : ℝ) = (5 : ℝ) ^ x) :
    ¬ Irrational x := by
  intro hxirr
  have hx0 : 0 ≤ x := nonneg_of_two_rpow_integer h₂
  let K : ℝ := (Real.log 2 + Real.log 3 + Real.log 5) * (1 + x)
  obtain ⟨D, hD⟩ := exists_nat_ge K
  let N : ℕ := 192 * D + 3
  let n : ℕ := 2 * N
  let m : ℕ := n ^ 6
  let r : ℕ := 32 * N ^ 6
  let C : ℕ := D * n ^ 5

  have hDN : 192 * D ≤ N := by
    dsimp only [N]
    omega
  have hNpos : 0 < N := by
    dsimp only [N]
    omega
  have hm : m = 2 * r := by
    dsimp only [m, r, n]
    ring
  have hr : 2 < r := by
    have hpow : 0 < N ^ 6 := pow_pos hNpos _
    dsimp only [r]
    omega
  have hCr : 192 * C ≤ r := by
    calc
      192 * C = (192 * D) * (32 * N ^ 5) := by
        dsimp only [C, n]
        ring
      _ ≤ N * (32 * N ^ 5) := Nat.mul_le_mul_right _ hDN
      _ = r := by
        dsimp only [r]
        ring
  have hrm : r ≤ m := by omega
  obtain ⟨hsmall, hnumeric⟩ := exponential_det_numeric_bound C m r hm hr hCr

  have hcard : Fintype.card (SixBox n) = m := by
    rw [card_sixBox]
  let e : Fin m ≃ SixBox n := (Fintype.equivFinOfCardEq hcard).symm
  let a : Fin m → ℝ := fun i ↦ rowArg (e i)
  let b : Fin m → ℝ := fun j ↦ colArg x (e j)
  let A : Matrix (Fin m) (Fin m) ℝ := fun i j ↦ Real.exp (a i * b j)

  have ha : Function.Injective a := (rowArg_injective n).comp e.injective
  have hb : Function.Injective b := (colArg_injective hxirr n).comp e.injective
  have hAne : A.det ≠ 0 := by
    exact det_exp_mul_ne_zero_of_injective a b ha hb
  have hAint : ∀ i j, ∃ z : ℤ, (z : ℝ) = A i j := by
    intro i j
    exact exp_rowArg_mul_colArg_integer h₂ h₃ h₅ (e i) (e j)
  have hlower : 1 ≤ |A.det| := one_le_abs_det_of_integer_entries A hAint hAne

  have hkernel : ∀ i j, |a i * b j| ≤ (C : ℝ) := by
    intro i j
    change |rowArg (e i) * colArg x (e j)| ≤ (C : ℝ)
    simpa only [C] using
      (abs_rowArg_mul_colArg_le hx0 (by simpa only [K] using hD) (e i) (e j))
  have hupper : |A.det| ≤
      (2 : ℝ) ^ m * (m.factorial : ℝ) * Real.exp (C : ℝ) ^ r *
        (Real.exp (C : ℝ) * (C : ℝ) ^ r / (r.factorial : ℝ)) ^ (m - r) := by
    change |Matrix.det (fun i j ↦ Real.exp (a i * b j))| ≤ _
    exact abs_det_exp_mul_le hrm a b (C : ℝ) (Nat.cast_nonneg _) hkernel hsmall
  have hdet_lt : |A.det| < 1 := hupper.trans_lt (by
    simpa only [mul_div_assoc] using hnumeric)
  exact (not_lt_of_ge hlower) hdet_lt

/-- Under the three integrality hypotheses, the exponent is rational. -/
theorem rational_of_two_three_five_rpow_integer {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (h₅ : ∃ z : ℤ, (z : ℝ) = (5 : ℝ) ^ x) :
    x ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  exact not_not.mp (not_irrational_of_three_prime_rpows_integer h₂ h₃ h₅)

/-- A rational exponent whose power of two is an integer must itself be an integer. -/
private theorem integer_of_rational_of_two_rpow_integer
    {x : ℝ} (hxrat : x ∈ Set.range ((↑) : ℚ → ℝ))
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  rcases hxrat with ⟨q, rfl⟩
  rcases h₂ with ⟨z, hz⟩
  have hxnonneg : 0 ≤ (q : ℝ) := by
    by_contra hx
    have hp : 0 < (2 : ℝ) ^ (q : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    have hlt : (2 : ℝ) ^ (q : ℝ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (lt_of_not_ge hx)
    have hzpos : 0 < z := by exact_mod_cast (hz.symm ▸ hp)
    have hzone : z < 1 := by exact_mod_cast (hz.symm ▸ hlt)
    omega
  have hqnonneg : 0 ≤ q := by exact_mod_cast hxnonneg
  have hzpos : 0 < z := by
    exact_mod_cast (hz.symm ▸ Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (q : ℝ))
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hzpos.le
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (Rat.num_nonneg.mpr hqnonneg)
  let d := q.den
  have hd : d ≠ 0 := q.den_nz
  have hqd : (q : ℝ) * (d : ℝ) = (m : ℝ) := by
    rw [Rat.cast_def, hm]
    field_simp
    simp [d, mul_comm]
  have hpow_real : ((2 : ℝ) ^ m) = (a : ℝ) ^ d := by
    calc
      ((2 : ℝ) ^ m) = (2 : ℝ) ^ ((q : ℝ) * (d : ℝ)) := by
        rw [hqd, Real.rpow_natCast]
      _ = ((2 : ℝ) ^ (q : ℝ)) ^ d := by
        rw [Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (a : ℝ) ^ d := by rw [← hz]; norm_cast
  have hpow_nat : 2 ^ m = a ^ d := by exact_mod_cast hpow_real
  have hdvdm : d ∣ m :=
    Nat.exponent_dvd_of_prime_pow_eq_pow Nat.prime_two hpow_nat
  have hcop : m.Coprime d := by
    simpa [d, hm] using q.reduced
  have hden : q.den = 1 := by
    change d = 1
    exact Nat.eq_one_of_dvd_coprimes hcop hdvdm dvd_rfl
  refine ⟨q.num, ?_⟩
  norm_cast
  exact Rat.coe_int_num_of_den_eq_one hden

/-- **Integer exponent theorem.**  If `2 ^ x`, `3 ^ x`, and `5 ^ x` are all integers,
then the real number `x` is an integer. -/
theorem integer_of_two_three_five_rpow_integer {x : ℝ}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (h₅ : (5 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ)) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  apply integer_of_rational_of_two_rpow_integer
  · exact rational_of_two_three_five_rpow_integer h₂ h₃ h₅
  · exact h₂

end


end LeanProofs.IntegerExponent
