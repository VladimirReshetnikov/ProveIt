import ExponentialIdentities.TwoBaseIntegerExponent.ThreeSmooth
import ExponentialIdentities.IntegerExponent.DeterminantBound

open scoped BigOperators Nat

namespace LeanProofs

namespace IntegerExponent

open Matrix

/-- A nonzero determinant with entries having a common positive natural denominator `Q`
has absolute value at least `Q⁻ᵐ`, where `m` is the matrix size. -/
theorem one_div_pow_le_abs_det_of_common_denominator
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (Q : ℕ) (hQ : 0 < Q)
    (hA : ∀ i j, ∃ z : ℤ, (z : ℝ) = (Q : ℝ) * A i j)
    (hne : A.det ≠ 0) :
    1 / (Q : ℝ) ^ Fintype.card ι ≤ |A.det| := by
  let B : Matrix ι ι ℝ := (Q : ℝ) • A
  have hBint : ∀ i j, ∃ z : ℤ, (z : ℝ) = B i j := by
    intro i j
    change ∃ z : ℤ, (z : ℝ) = (Q : ℝ) * A i j
    exact hA i j
  have hBdet : B.det = (Q : ℝ) ^ Fintype.card ι * A.det := by
    dsimp only [B]
    exact Matrix.det_smul A (Q : ℝ)
  have hBne : B.det ≠ 0 := by
    rw [hBdet]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hQ.ne')) hne
  have hlower : 1 ≤ |B.det| :=
    one_le_abs_det_of_integer_entries B hBint hBne
  rw [hBdet, abs_mul,
    abs_of_pos (pow_pos (by exact_mod_cast hQ) _)] at hlower
  apply (div_le_iff₀ (pow_pos (by exact_mod_cast hQ) _)).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hlower

/-- The determinant upper bound retains enough of its explicit power-of-two margin to
absorb an additional natural denominator `b ^ s`. -/
theorem exponential_det_numeric_bound_with_denominator
    (C m r b s : ℕ) (hm : m = 2 * r) (hr : 2 < r) (hCr : 192 * C ≤ r)
    (hmargin : b * s + 2 * r < r * r) :
    (C : ℝ) ^ r / (r.factorial : ℝ) ≤ 1 ∧
      (b : ℝ) ^ s *
        ((2 : ℝ) ^ m * (m.factorial : ℝ) * Real.exp (C : ℝ) ^ r *
          (Real.exp (C : ℝ) * ((C : ℝ) ^ r / (r.factorial : ℝ))) ^ (m - r)) < 1 := by
  subst m
  have hr0 : 0 < r := by omega
  let q : ℝ := (C : ℝ) ^ r / (r.factorial : ℝ)
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    positivity
  have htail : q ≤ ((1 : ℝ) / 64) ^ r := by
    exact pow_div_factorial_le_inv64_pow C r hr0 hCr
  have hsmall : q ≤ 1 := htail.trans (pow_le_one₀ (by norm_num) (by norm_num))
  have hfacNat : (2 * r).factorial ≤ 2 ^ (4 * r * r) := by
    calc
      (2 * r).factorial ≤ (2 * r) ^ (2 * r) := Nat.factorial_le_pow _
      _ ≤ (2 ^ (2 * r)) ^ (2 * r) :=
        pow_le_pow_left₀ (Nat.zero_le _) (Nat.le_of_lt (2 * r).lt_two_pow_self) _
      _ = 2 ^ (4 * r * r) := by
        rw [← pow_mul]
        congr 1
        ring
  have hfac : ((2 * r).factorial : ℝ) ≤ (2 : ℝ) ^ (4 * r * r) := by
    exact_mod_cast hfacNat
  have hexpBase : Real.exp (C : ℝ) ≤ (4 : ℝ) ^ C := by
    calc
      Real.exp (C : ℝ) = Real.exp 1 ^ C := by
        rw [← Real.exp_nat_mul]
        simp
      _ ≤ (3 : ℝ) ^ C :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le C
      _ ≤ (4 : ℝ) ^ C := pow_le_pow_left₀ (by norm_num) (by norm_num) C
  have hfourC : 4 * C ≤ r := by omega
  have hExpExponent : 4 * C * r ≤ r * r := Nat.mul_le_mul_right r hfourC
  have hexpPow : Real.exp (C : ℝ) ^ (2 * r) ≤ (2 : ℝ) ^ (r * r) := by
    calc
      Real.exp (C : ℝ) ^ (2 * r) ≤ ((4 : ℝ) ^ C) ^ (2 * r) :=
        pow_le_pow_left₀ (Real.exp_pos _).le hexpBase _
      _ = (2 : ℝ) ^ (4 * C * r) := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, ← pow_mul]
        congr 1
        ring
      _ ≤ (2 : ℝ) ^ (r * r) := pow_le_pow_right₀ (by norm_num) hExpExponent
  have htailPow : q ^ r ≤ (((1 : ℝ) / 64) ^ r) ^ r :=
    pow_le_pow_left₀ hq0 htail r
  have htwoRsub : 2 * r - r = r := by omega
  have hrearrange :
      (2 : ℝ) ^ (2 * r) * ((2 * r).factorial : ℝ) * Real.exp (C : ℝ) ^ r *
          (Real.exp (C : ℝ) * q) ^ r =
        (2 : ℝ) ^ (2 * r) * ((2 * r).factorial : ℝ) *
          Real.exp (C : ℝ) ^ (2 * r) * q ^ r := by
    rw [mul_pow]
    have hexpCombine : Real.exp (C : ℝ) ^ r * Real.exp (C : ℝ) ^ r =
        Real.exp (C : ℝ) ^ (2 * r) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      (2 : ℝ) ^ (2 * r) * ((2 * r).factorial : ℝ) * Real.exp (C : ℝ) ^ r *
          (Real.exp (C : ℝ) ^ r * q ^ r) =
        ((2 : ℝ) ^ (2 * r) * ((2 * r).factorial : ℝ)) *
          (Real.exp (C : ℝ) ^ r * Real.exp (C : ℝ) ^ r) * q ^ r := by ring
      _ = (2 : ℝ) ^ (2 * r) * ((2 * r).factorial : ℝ) *
          Real.exp (C : ℝ) ^ (2 * r) * q ^ r := by rw [hexpCombine]
  have hcoarse :
      (2 : ℝ) ^ (2 * r) * ((2 * r).factorial : ℝ) *
          Real.exp (C : ℝ) ^ (2 * r) * q ^ r ≤
        (2 : ℝ) ^ (2 * r) * (2 : ℝ) ^ (4 * r * r) *
          (2 : ℝ) ^ (r * r) * (((1 : ℝ) / 64) ^ r) ^ r := by
    have h₁ :
        (2 : ℝ) ^ (2 * r) * ((2 * r).factorial : ℝ) ≤
          (2 : ℝ) ^ (2 * r) * (2 : ℝ) ^ (4 * r * r) :=
      mul_le_mul_of_nonneg_left hfac (pow_nonneg (by norm_num) _)
    have h₂ :
        (2 : ℝ) ^ (2 * r) * ((2 * r).factorial : ℝ) *
            Real.exp (C : ℝ) ^ (2 * r) ≤
          (2 : ℝ) ^ (2 * r) * (2 : ℝ) ^ (4 * r * r) *
            (2 : ℝ) ^ (r * r) :=
      mul_le_mul h₁ hexpPow (pow_nonneg (Real.exp_pos _).le _)
        (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _))
    exact mul_le_mul h₂ htailPow (pow_nonneg hq0 _)
      (mul_nonneg
        (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _))
        (pow_nonneg (by norm_num) _))
  have hinvPow : (((1 : ℝ) / 64) ^ r) ^ r =
      1 / (2 : ℝ) ^ (6 * r * r) := by
    rw [← pow_mul, div_pow]
    simp only [one_pow]
    rw [show (64 : ℝ) = (2 : ℝ) ^ 6 by norm_num, ← pow_mul]
    have h₆ : 6 * (r * r) = 6 * r * r := by ring
    rw [h₆]
  have hnum :
      (2 : ℝ) ^ (2 * r) * (2 : ℝ) ^ (4 * r * r) * (2 : ℝ) ^ (r * r) =
        (2 : ℝ) ^ (2 * r + 5 * r * r) := by
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  have hbNat : b ≤ 2 ^ b := Nat.le_of_lt b.lt_two_pow_self
  have hbPowNat : b ^ s ≤ 2 ^ (b * s) := by
    calc
      b ^ s ≤ (2 ^ b) ^ s := pow_le_pow_left₀ (Nat.zero_le _) hbNat s
      _ = 2 ^ (b * s) := by rw [← pow_mul]
  have hbPow : (b : ℝ) ^ s ≤ (2 : ℝ) ^ (b * s) := by
    exact_mod_cast hbPowNat
  have hExponentLt : b * s + (2 * r + 5 * r * r) < 6 * r * r := by
    calc
      b * s + (2 * r + 5 * r * r) = (b * s + 2 * r) + 5 * r * r := by ring
      _ < r * r + 5 * r * r := Nat.add_lt_add_right hmargin _
      _ = 6 * r * r := by ring
  have hpowLt :
      (2 : ℝ) ^ (b * s + (2 * r + 5 * r * r)) < (2 : ℝ) ^ (6 * r * r) :=
    pow_lt_pow_right₀ (by norm_num) hExponentLt
  refine ⟨hsmall, ?_⟩
  change (b : ℝ) ^ s *
      ((2 : ℝ) ^ (2 * r) * ((2 * r).factorial : ℝ) * Real.exp (C : ℝ) ^ r *
        (Real.exp (C : ℝ) * q) ^ (2 * r - r)) < 1
  rw [htwoRsub, hrearrange]
  calc
    (b : ℝ) ^ s *
        ((2 : ℝ) ^ (2 * r) * ((2 * r).factorial : ℝ) *
          Real.exp (C : ℝ) ^ (2 * r) * q ^ r) ≤
      (b : ℝ) ^ s *
        ((2 : ℝ) ^ (2 * r) * (2 : ℝ) ^ (4 * r * r) *
          (2 : ℝ) ^ (r * r) * (((1 : ℝ) / 64) ^ r) ^ r) :=
      mul_le_mul_of_nonneg_left hcoarse (pow_nonneg (Nat.cast_nonneg _) _)
    _ = (b : ℝ) ^ s *
        ((2 : ℝ) ^ (2 * r + 5 * r * r) / (2 : ℝ) ^ (6 * r * r)) := by
      rw [hinvPow, hnum]
      simp only [div_eq_mul_inv, one_mul, mul_assoc]
    _ ≤ (2 : ℝ) ^ (b * s + (2 * r + 5 * r * r)) /
        (2 : ℝ) ^ (6 * r * r) := by
      rw [div_eq_mul_inv]
      calc
        (b : ℝ) ^ s *
            ((2 : ℝ) ^ (2 * r + 5 * r * r) *
              ((2 : ℝ) ^ (6 * r * r))⁻¹) =
            ((b : ℝ) ^ s * (2 : ℝ) ^ (2 * r + 5 * r * r)) *
              ((2 : ℝ) ^ (6 * r * r))⁻¹ := by ring
        _ ≤ ((2 : ℝ) ^ (b * s) * (2 : ℝ) ^ (2 * r + 5 * r * r)) *
              ((2 : ℝ) ^ (6 * r * r))⁻¹ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hbPow (pow_nonneg (by norm_num) _))
            (inv_nonneg.mpr (pow_nonneg (by norm_num) _))
        _ = (2 : ℝ) ^ (b * s + (2 * r + 5 * r * r)) *
              ((2 : ℝ) ^ (6 * r * r))⁻¹ := by rw [← pow_add]
    _ < 1 := (div_lt_one (pow_pos (by norm_num) _)).2 hpowLt

end IntegerExponent

namespace TwoBaseIntegerExponent

open Set

noncomputable section

/-- Multiplying a rational number by a natural multiple of its denominator gives an
integer-valued real number. -/
theorem rat_mul_nat_mem_intCast_of_den_dvd {q : ℚ} {M : ℕ} (hM : q.den ∣ M) :
    (q : ℝ) * (M : ℝ) ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨t, rfl⟩ := hM
  refine ⟨q.num * (t : ℤ), ?_⟩
  rw [Rat.cast_def]
  push_cast
  field_simp

/-- Adjoining fixed powers of `2` and `3` to the third base preserves injectivity of
the three monomial coordinates. -/
theorem monomial_injective_mul_two_pow_three_pow
    {a : ℕ}
    (hmono : Function.Injective
      (fun s : ℕ × ℕ × ℕ ↦ 2 ^ s.1 * 3 ^ s.2.1 * a ^ s.2.2))
    (u v : ℕ) :
    Function.Injective
      (fun s : ℕ × ℕ × ℕ ↦
        2 ^ s.1 * 3 ^ s.2.1 * (2 ^ u * 3 ^ v * a) ^ s.2.2) := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  have hexpand (i j k : ℕ) :
      2 ^ i * 3 ^ j * (2 ^ u * 3 ^ v * a) ^ k =
        2 ^ (i + u * k) * 3 ^ (j + v * k) * a ^ k := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add, pow_add]
    ring
  change 2 ^ i * 3 ^ j * (2 ^ u * 3 ^ v * a) ^ k =
    2 ^ i' * 3 ^ j' * (2 ^ u * 3 ^ v * a) ^ k' at h
  rw [hexpand, hexpand] at h
  have huv := hmono
    (a₁ := ((i + u * k, j + v * k, k) : ℕ × ℕ × ℕ))
    (a₂ := ((i' + u * k', j' + v * k', k') : ℕ × ℕ × ℕ)) h
  simp only [Prod.mk.injEq] at huv
  have hk : k = k' := huv.2.2
  subst k'
  have hi : i = i' := by omega
  have hj : j = j' := by omega
  subst i'
  subst j'
  rfl

/-- Rational third-base output suffices for the six-exponentials conclusion whenever its
reduced denominator is canceled by a product of powers of the two integral outputs. -/
theorem rational_of_two_three_a_rpow_rational_of_den_dvd_outputs
    {a : ℕ} (ha : 1 < a)
    (hmono : Function.Injective
      (fun s : ℕ × ℕ × ℕ ↦ 2 ^ s.1 * 3 ^ s.2.1 * a ^ s.2.2))
    {x : ℝ} {m₂ m₃ : ℕ}
    (h₂ : (m₂ : ℝ) = (2 : ℝ) ^ x)
    (h₃ : (m₃ : ℝ) = (3 : ℝ) ^ x)
    {q : ℚ} (haPow : (q : ℝ) = (a : ℝ) ^ x)
    (hden : ∃ u v : ℕ, q.den ∣ m₂ ^ u * m₃ ^ v) :
    x ∈ Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨u, v, hden⟩ := hden
  let A : ℕ := 2 ^ u * 3 ^ v * a
  have hA : 1 < A := by
    dsimp only [A]
    have : a ≤ 2 ^ u * 3 ^ v * a := by
      have hone : 1 ≤ 2 ^ u * 3 ^ v :=
        Nat.one_le_iff_ne_zero.mpr
          (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
      nlinarith
    omega
  have hmonoA : Function.Injective
      (fun s : ℕ × ℕ × ℕ ↦ 2 ^ s.1 * 3 ^ s.2.1 * A ^ s.2.2) := by
    simpa only [A] using monomial_injective_mul_two_pow_three_pow hmono u v
  have h₂int : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x := by
    exact ⟨(m₂ : ℤ), by simpa using h₂⟩
  have h₃int : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x := by
    exact ⟨(m₃ : ℤ), by simpa using h₃⟩
  obtain ⟨z, hz⟩ := rat_mul_nat_mem_intCast_of_den_dvd hden
  have hApow : (A : ℝ) ^ x = (q : ℝ) * (m₂ ^ u * m₃ ^ v : ℕ) := by
    dsimp only [A]
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) x u,
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) x v]
    rw [← h₂, ← h₃, ← haPow]
    ring
  have hAint : ∃ z : ℤ, (z : ℝ) = (A : ℝ) ^ x :=
    ⟨z, hz.trans hApow.symm⟩
  exact rational_of_two_three_a_rpow_integer_of_monomial_injective
    hA hmonoA h₂int h₃int hAint

/-- Under the same denominator-clearing condition, the rationality conclusion upgrades to
integrality because the power of two is integral. -/
theorem integer_of_two_three_a_rpow_rational_of_den_dvd_outputs
    {a : ℕ} (ha : 1 < a)
    (hmono : Function.Injective
      (fun s : ℕ × ℕ × ℕ ↦ 2 ^ s.1 * 3 ^ s.2.1 * a ^ s.2.2))
    {x : ℝ} {m₂ m₃ : ℕ}
    (h₂ : (m₂ : ℝ) = (2 : ℝ) ^ x)
    (h₃ : (m₃ : ℝ) = (3 : ℝ) ^ x)
    {q : ℚ} (haPow : (q : ℝ) = (a : ℝ) ^ x)
    (hden : ∃ u v : ℕ, q.den ∣ m₂ ^ u * m₃ ^ v) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  apply IntegerExponent.integer_of_rational_of_two_rpow_integer
  · exact rational_of_two_three_a_rpow_rational_of_den_dvd_outputs
      ha hmono h₂ h₃ haPow hden
  · exact ⟨(m₂ : ℤ), by simpa using h₂⟩

/-- Concrete prime-factor form: if `a` has a prime divisor other than `2` and `3`, a
rational `a ^ x` whose denominator is supported by the two integral outputs forces `x`
to be an integer. -/
theorem integer_of_two_three_a_rpow_rational_of_prime_factor_of_den_dvd_outputs
    {a p : ℕ} (ha : 0 < a) (hp : p.Prime) (hpa : p ∣ a)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {x : ℝ} {m₂ m₃ : ℕ}
    (h₂ : (m₂ : ℝ) = (2 : ℝ) ^ x)
    (h₃ : (m₃ : ℝ) = (3 : ℝ) ^ x)
    {q : ℚ} (haPow : (q : ℝ) = (a : ℝ) ^ x)
    (hden : ∃ u v : ℕ, q.den ∣ m₂ ^ u * m₃ ^ v) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  have ha1 : 1 < a := hp.one_lt.trans_le (Nat.le_of_dvd ha hpa)
  exact integer_of_two_three_a_rpow_rational_of_den_dvd_outputs ha1
    (monomial_injective_of_prime_dvd_ne_two_three ha hp hpa hp2 hp3)
    h₂ h₃ haPow hden

end

end TwoBaseIntegerExponent

end LeanProofs
