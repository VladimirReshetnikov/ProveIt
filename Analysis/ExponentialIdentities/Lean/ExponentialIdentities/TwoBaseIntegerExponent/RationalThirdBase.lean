import ExponentialIdentities.TwoBaseIntegerExponent.ThreeSmooth
import ExponentialIdentities.TwoBaseIntegerExponent.LeastSolution
import ExponentialIdentities.IntegerExponent.DeterminantBound

/-!
# Rational output at a third base

This module extends the three-base interpolation determinant from an integral third output
to a rational one. A uniform denominator bound for the determinant entries is absorbed by
an explicit power-of-two margin in the analytic estimate. It follows that, under a
nonintegral two-base solution, the positive natural bases with rational output are exactly
the products of powers of `2` and `3`.
-/

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

private abbrev RationalRowBox (n : ℕ) :=
  Fin (n * n) × Fin (n * n) × Fin (n * n)

private abbrev RationalColBox (n : ℕ) :=
  Fin ((n * n) * n) × Fin ((n * n) * n)

private theorem card_rationalRowBox (n : ℕ) :
    Fintype.card (RationalRowBox n) = n ^ 6 := by
  simp [RationalRowBox]
  ring

private theorem card_rationalColBox (n : ℕ) :
    Fintype.card (RationalColBox n) = n ^ 6 := by
  simp [RationalColBox]
  ring

private def rationalRowNat (a : ℕ) {n : ℕ} (i : RationalRowBox n) : ℕ :=
  2 ^ (i.1 : ℕ) * 3 ^ (i.2.1 : ℕ) * a ^ (i.2.2 : ℕ)

private def rationalRowArg (a : ℕ) {n : ℕ} (i : RationalRowBox n) : ℝ :=
  Real.log (rationalRowNat a i : ℝ)

private def rationalColArg {n : ℕ} (x : ℝ) (j : RationalColBox n) : ℝ :=
  (j.1 : ℝ) + (j.2 : ℝ) * x

private theorem rationalRowNat_injective {a n : ℕ}
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2.1 * a ^ u.2.2)) :
    Function.Injective (@rationalRowNat a n) := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  have huv : ((i : ℕ), (j : ℕ), (k : ℕ)) =
      ((i' : ℕ), (j' : ℕ), (k' : ℕ)) := hmono h
  simp only [Prod.mk.injEq] at huv
  exact Prod.ext (Fin.ext huv.1) (Prod.ext (Fin.ext huv.2.1) (Fin.ext huv.2.2))

private theorem rationalColArg_injective {x : ℝ} (hx : Irrational x) (n : ℕ) :
    Function.Injective (@rationalColArg n x) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have huv : ((i : ℕ), (j : ℕ)) = ((i' : ℕ), (j' : ℕ)) :=
    IntegerExponent.Irrational.injective_nat_add_mul hx h
  simp only [Prod.mk.injEq] at huv
  exact Prod.ext (Fin.ext huv.1) (Fin.ext huv.2)

private theorem rationalRowNat_pos {a n : ℕ} (ha : 0 < a)
    (i : RationalRowBox n) : 0 < rationalRowNat a i := by
  unfold rationalRowNat
  positivity

private theorem rationalRowArg_injective {a : ℕ} (ha : 0 < a)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2.1 * a ^ u.2.2))
    (n : ℕ) : Function.Injective (@rationalRowArg a n) := by
  intro i j h
  apply rationalRowNat_injective hmono
  have hc : (rationalRowNat a i : ℝ) = (rationalRowNat a j : ℝ) :=
    Real.log_injOn_pos
      (show 0 < (rationalRowNat a i : ℝ) by
        exact_mod_cast rationalRowNat_pos ha i)
      (show 0 < (rationalRowNat a j : ℝ) by
        exact_mod_cast rationalRowNat_pos ha j) h
  exact Nat.cast_injective hc

private theorem rationalRowArg_nonneg {a n : ℕ} (ha : 0 < a)
    (i : RationalRowBox n) : 0 ≤ rationalRowArg a i := by
  apply Real.log_nonneg
  exact_mod_cast rationalRowNat_pos ha i

private theorem rationalRowArg_le {a n : ℕ} (ha : 1 ≤ a)
    (i : RationalRowBox n) :
    rationalRowArg a i ≤
      (n * n : ℕ) * (Real.log 2 + Real.log 3 + Real.log a) := by
  have hu₂ : ((i.1 : ℕ) : ℝ) ≤ (n * n : ℕ) := by exact_mod_cast i.1.isLt.le
  have hu₃ : ((i.2.1 : ℕ) : ℝ) ≤ (n * n : ℕ) := by
    exact_mod_cast i.2.1.isLt.le
  have hua : ((i.2.2 : ℕ) : ℝ) ≤ (n * n : ℕ) := by
    exact_mod_cast i.2.2.isLt.le
  have hlog₂ : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog₃ : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hloga : 0 ≤ Real.log a := Real.log_nonneg (by exact_mod_cast ha)
  have hterm₂ : ((i.1 : ℕ) : ℝ) * Real.log 2 ≤
      ((n * n : ℕ) : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right hu₂ hlog₂
  have hterm₃ : ((i.2.1 : ℕ) : ℝ) * Real.log 3 ≤
      ((n * n : ℕ) : ℝ) * Real.log 3 := mul_le_mul_of_nonneg_right hu₃ hlog₃
  have hterma : ((i.2.2 : ℕ) : ℝ) * Real.log a ≤
      ((n * n : ℕ) : ℝ) * Real.log a := mul_le_mul_of_nonneg_right hua hloga
  have hexpand : rationalRowArg a i =
      ((i.1 : ℕ) : ℝ) * Real.log 2 +
      ((i.2.1 : ℕ) : ℝ) * Real.log 3 +
      ((i.2.2 : ℕ) : ℝ) * Real.log a := by
    simp only [rationalRowArg, rationalRowNat, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
  rw [hexpand]
  linarith

private theorem rationalColArg_nonneg {n : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (j : RationalColBox n) : 0 ≤ rationalColArg x j := by
  dsimp only [rationalColArg]
  positivity

private theorem rationalColArg_le {n : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (j : RationalColBox n) :
    rationalColArg x j ≤ ((n * n) * n : ℕ) * (1 + x) := by
  have hv₀ : ((j.1 : ℕ) : ℝ) ≤ ((n * n) * n : ℕ) := by
    exact_mod_cast j.1.isLt.le
  have hv₁ : ((j.2 : ℕ) : ℝ) ≤ ((n * n) * n : ℕ) := by
    exact_mod_cast j.2.isLt.le
  have hv₁x : ((j.2 : ℕ) : ℝ) * x ≤
      (((n * n) * n : ℕ) : ℝ) * x := mul_le_mul_of_nonneg_right hv₁ hx
  dsimp only [rationalColArg]
  linarith

private theorem rational_abs_rowArg_mul_colArg_le {a n D : ℕ} {x : ℝ}
    (ha : 1 < a) (hx : 0 ≤ x)
    (hD : (Real.log 2 + Real.log 3 + Real.log a) * (1 + x) ≤ D)
    (i : RationalRowBox n) (j : RationalColBox n) :
    |rationalRowArg a i * rationalColArg x j| ≤ (D * n ^ 5 : ℕ) := by
  have hrow0 := rationalRowArg_nonneg (by omega : 0 < a) i
  have hcol0 := rationalColArg_nonneg hx j
  have hrow := rationalRowArg_le ha.le i
  have hcol := rationalColArg_le hx j
  rw [abs_of_nonneg (mul_nonneg hrow0 hcol0)]
  calc
    rationalRowArg a i * rationalColArg x j ≤
        ((n * n : ℕ) : ℝ) * (Real.log 2 + Real.log 3 + Real.log a) *
          (((n * n) * n : ℕ) * (1 + x)) :=
      mul_le_mul hrow hcol hcol0
        (mul_nonneg (Nat.cast_nonneg _) (by positivity))
    _ = ((n ^ 5 : ℕ) : ℝ) *
        ((Real.log 2 + Real.log 3 + Real.log a) * (1 + x)) := by
      push_cast
      ring
    _ ≤ ((n ^ 5 : ℕ) : ℝ) * D :=
      mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg _)
    _ = (D * n ^ 5 : ℕ) := by
      push_cast
      ring

private theorem rat_pow_mul_den_pow_mem_intCast {q : ℚ} {e L : ℕ}
    (hle : e ≤ L) :
    (q.den : ℝ) ^ L * (q : ℝ) ^ e ∈ Set.range ((↑) : ℤ → ℝ) := by
  refine ⟨q.num ^ e * (q.den : ℤ) ^ (L - e), ?_⟩
  rw [Rat.cast_def]
  push_cast
  rw [div_pow]
  have hden0R : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  rw [show L = e + (L - e) by omega, pow_add]
  field_simp
  simp

private theorem rationalProduct_rpow_eq {a : ℕ} (ha : 0 < a)
    {x : ℝ} {z₂ z₃ : ℤ} {q : ℚ}
    (h₂ : (z₂ : ℝ) = (2 : ℝ) ^ x)
    (h₃ : (z₃ : ℝ) = (3 : ℝ) ^ x)
    (haPow : (q : ℝ) = (a : ℝ) ^ x)
    (u₂ u₃ ua : ℕ) :
    (((2 ^ u₂ * 3 ^ u₃ * a ^ ua : ℕ) : ℝ) ^ x) =
      (z₂ : ℝ) ^ u₂ * (z₃ : ℝ) ^ u₃ * (q : ℝ) ^ ua := by
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) x u₂,
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) x u₃,
    ← Real.rpow_pow_comm (by exact_mod_cast ha.le) x ua]
  rw [← h₂, ← h₃, ← haPow]

private theorem rational_exp_log_mul_nat_add_eq {R : ℕ} (hR : 0 < R)
    {x : ℝ} (v₀ v₁ : ℕ) :
    Real.exp (Real.log (R : ℝ) * ((v₀ : ℝ) + (v₁ : ℝ) * x)) =
      (R : ℝ) ^ v₀ * ((R : ℝ) ^ x) ^ v₁ := by
  rw [← Real.rpow_def_of_pos (by exact_mod_cast hR)]
  rw [Real.rpow_add (by exact_mod_cast hR)]
  rw [Real.rpow_natCast]
  rw [show (v₁ : ℝ) * x = x * (v₁ : ℝ) by ring]
  rw [Real.rpow_mul_natCast (by exact_mod_cast hR.le)]

private theorem rational_denominator_exponent_le {n : ℕ}
    (i : RationalRowBox n) (j : RationalColBox n) :
    (i.2.2 : ℕ) * (j.2 : ℕ) ≤ n ^ 5 := by
  calc
    (i.2.2 : ℕ) * (j.2 : ℕ) ≤ (n * n) * ((n * n) * n) :=
      Nat.mul_le_mul i.2.2.isLt.le j.2.isLt.le
    _ = n ^ 5 := by ring

private theorem rational_exp_rowArg_mul_colArg_common_denominator
    {a n : ℕ} (ha : 0 < a) {x : ℝ} {z₂ z₃ : ℤ} {q : ℚ}
    (h₂ : (z₂ : ℝ) = (2 : ℝ) ^ x)
    (h₃ : (z₃ : ℝ) = (3 : ℝ) ^ x)
    (haPow : (q : ℝ) = (a : ℝ) ^ x)
    (i : RationalRowBox n) (j : RationalColBox n) :
    ∃ z : ℤ, (z : ℝ) = (q.den : ℝ) ^ (n ^ 5) *
      Real.exp (rationalRowArg a i * rationalColArg x j) := by
  let R : ℕ := rationalRowNat a i
  let u₂ : ℕ := i.1
  let u₃ : ℕ := i.2.1
  let ua : ℕ := i.2.2
  let v₀ : ℕ := j.1
  let v₁ : ℕ := j.2
  have hR : 0 < R := rationalRowNat_pos ha i
  have hle : ua * v₁ ≤ n ^ 5 := rational_denominator_exponent_le i j
  obtain ⟨zq, hzq⟩ := rat_pow_mul_den_pow_mem_intCast
    (q := q) (e := ua * v₁) (L := n ^ 5) hle
  refine ⟨(R : ℤ) ^ v₀ * z₂ ^ (u₂ * v₁) * z₃ ^ (u₃ * v₁) * zq, ?_⟩
  change (((R : ℤ) ^ v₀ * z₂ ^ (u₂ * v₁) * z₃ ^ (u₃ * v₁) * zq : ℤ) : ℝ) =
    (q.den : ℝ) ^ (n ^ 5) *
      Real.exp (Real.log (R : ℝ) * ((v₀ : ℝ) + (v₁ : ℝ) * x))
  rw [rational_exp_log_mul_nat_add_eq hR]
  rw [show R = 2 ^ u₂ * 3 ^ u₃ * a ^ ua by rfl]
  rw [rationalProduct_rpow_eq ha h₂ h₃ haPow]
  push_cast
  rw [hzq]
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
  ring

private theorem not_irrational_of_two_three_a_rpow_rational_of_monomial_injective
    {a : ℕ} (ha : 1 < a)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2.1 * a ^ u.2.2))
    {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (haPow : ∃ q : ℚ, (q : ℝ) = (a : ℝ) ^ x) :
    ¬ Irrational x := by
  classical
  intro hxirr
  obtain ⟨z₂, hz₂⟩ := h₂
  obtain ⟨z₃, hz₃⟩ := h₃
  obtain ⟨q, hq⟩ := haPow
  have hx0 : 0 ≤ x := IntegerExponent.nonneg_of_two_rpow_integer ⟨z₂, hz₂⟩
  let K : ℝ := (Real.log 2 + Real.log 3 + Real.log a) * (1 + x)
  obtain ⟨D, hD⟩ := exists_nat_ge K
  let b : ℕ := q.den
  let N : ℕ := 192 * D + 2 * b + 3
  let n : ℕ := 2 * N
  let m : ℕ := n ^ 6
  let r : ℕ := 32 * N ^ 6
  let C : ℕ := D * n ^ 5
  let s : ℕ := n ^ 11
  let Q : ℕ := b ^ (n ^ 5)

  have hbpos : 0 < b := by
    dsimp only [b]
    exact q.den_pos
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
  have hmargin : b * s + 2 * r < r * r := by
    have hbN : 32 * b + 1 < 16 * N := by
      dsimp only [N]
      omega
    have hN5pos : 0 < N ^ 5 := pow_pos hNpos _
    have hstep : 32 * b * N ^ 5 + 1 < 16 * N * N ^ 5 := by
      calc
        32 * b * N ^ 5 + 1 ≤ (32 * b + 1) * N ^ 5 := by
          nlinarith
        _ < (16 * N) * N ^ 5 := Nat.mul_lt_mul_of_pos_right hbN hN5pos
        _ = 16 * N * N ^ 5 := rfl
    have hscale : 0 < 64 * N ^ 6 := by positivity
    have hscaled := Nat.mul_lt_mul_of_pos_right hstep hscale
    change b * (2 * N) ^ 11 + 2 * (32 * N ^ 6) <
      (32 * N ^ 6) * (32 * N ^ 6)
    calc
      b * (2 * N) ^ 11 + 2 * (32 * N ^ 6) =
          (32 * b * N ^ 5 + 1) * (64 * N ^ 6) := by ring
      _ < (16 * N * N ^ 5) * (64 * N ^ 6) := hscaled
      _ = (32 * N ^ 6) * (32 * N ^ 6) := by ring
  have hrm : r ≤ m := by omega
  obtain ⟨hsmall, hnumeric⟩ :=
    IntegerExponent.exponential_det_numeric_bound_with_denominator
      C m r b s hm hr hCr hmargin

  have hrowcard : Fintype.card (RationalRowBox n) = m := by
    rw [card_rationalRowBox]
  have hcolcard : Fintype.card (RationalColBox n) = m := by
    rw [card_rationalColBox]
  let erow : Fin m ≃ RationalRowBox n := (Fintype.equivFinOfCardEq hrowcard).symm
  let ecol : Fin m ≃ RationalColBox n := (Fintype.equivFinOfCardEq hcolcard).symm
  let row : Fin m → ℝ := fun i ↦ rationalRowArg a (erow i)
  let col : Fin m → ℝ := fun j ↦ rationalColArg x (ecol j)
  let A : Matrix (Fin m) (Fin m) ℝ := fun i j ↦ Real.exp (row i * col j)

  have hrow : Function.Injective row :=
    (rationalRowArg_injective (by omega) hmono n).comp erow.injective
  have hcol : Function.Injective col :=
    (rationalColArg_injective hxirr n).comp ecol.injective
  have hAne : A.det ≠ 0 := by
    exact IntegerExponent.det_exp_mul_ne_zero_of_injective row col hrow hcol
  have hQpos : 0 < Q := by
    dsimp only [Q]
    exact pow_pos hbpos _
  have hAden : ∀ i j, ∃ z : ℤ, (z : ℝ) = (Q : ℝ) * A i j := by
    intro i j
    change ∃ z : ℤ, (z : ℝ) = (Q : ℝ) *
      Real.exp (rationalRowArg a (erow i) * rationalColArg x (ecol j))
    simpa only [Q, b, Nat.cast_pow] using
      (rational_exp_rowArg_mul_colArg_common_denominator
        (a := a) (n := n) (by omega) hz₂ hz₃ hq (erow i) (ecol j))
  have hlower : 1 / (Q : ℝ) ^ m ≤ |A.det| :=
    by
      simpa using
        (IntegerExponent.one_div_pow_le_abs_det_of_common_denominator
          A Q hQpos hAden hAne)

  have hkernel : ∀ i j, |row i * col j| ≤ (C : ℝ) := by
    intro i j
    change |rationalRowArg a (erow i) * rationalColArg x (ecol j)| ≤ (C : ℝ)
    simpa only [C] using
      (rational_abs_rowArg_mul_colArg_le ha hx0
        (by simpa only [K] using hD) (erow i) (ecol j))
  have hupper : |A.det| ≤
      (2 : ℝ) ^ m * (m.factorial : ℝ) * Real.exp (C : ℝ) ^ r *
        (Real.exp (C : ℝ) * (C : ℝ) ^ r / (r.factorial : ℝ)) ^ (m - r) := by
    change |Matrix.det (fun i j ↦ Real.exp (row i * col j))| ≤ _
    exact IntegerExponent.abs_det_exp_mul_le hrm row col (C : ℝ)
      (Nat.cast_nonneg _) hkernel hsmall
  have hQm : (Q : ℝ) ^ m = (b : ℝ) ^ s := by
    dsimp only [Q, m, s]
    push_cast
    rw [← pow_mul]
    have hexp : n ^ 5 * n ^ 6 = n ^ 11 := by
      rw [← pow_add]
    rw [hexp]
  have hdenpos : 0 < (b : ℝ) ^ s := pow_pos (by exact_mod_cast hbpos) _
  have hlowerS : 1 / (b : ℝ) ^ s ≤ |A.det| := by
    rw [← hQm]
    exact hlower
  have hone_le : 1 ≤ (b : ℝ) ^ s * |A.det| := by
    have h := (div_le_iff₀ hdenpos).mp hlowerS
    simpa [mul_comm] using h
  have hscaledUpper : (b : ℝ) ^ s * |A.det| ≤
      (b : ℝ) ^ s *
        ((2 : ℝ) ^ m * (m.factorial : ℝ) * Real.exp (C : ℝ) ^ r *
          (Real.exp (C : ℝ) * ((C : ℝ) ^ r / (r.factorial : ℝ))) ^ (m - r)) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
    simpa only [mul_div_assoc] using hupper
  have : (1 : ℝ) < 1 :=
    lt_of_le_of_lt (hone_le.trans hscaledUpper) hnumeric
  exact lt_irrefl 1 this

/-- **Unrestricted rational third-output theorem.** If the natural monomials in `2`, `3`,
and `a` are pairwise distinct, integral powers at `2` and `3` together with a rational
power at `a` force the real exponent to be rational. -/
theorem rational_of_two_three_a_rpow_rational_of_monomial_injective
    {a : ℕ} (ha : 1 < a)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2.1 * a ^ u.2.2))
    {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (haPow : ∃ q : ℚ, (q : ℝ) = (a : ℝ) ^ x) :
    x ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  exact not_not.mp
    (not_irrational_of_two_three_a_rpow_rational_of_monomial_injective
      ha hmono h₂ h₃ haPow)

/-- Under the same hypotheses, rationality upgrades to integrality because the power at
`2` is integral. -/
theorem integer_of_two_three_a_rpow_rational_of_monomial_injective
    {a : ℕ} (ha : 1 < a)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2.1 * a ^ u.2.2))
    {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (haPow : ∃ q : ℚ, (q : ℝ) = (a : ℝ) ^ x) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  apply IntegerExponent.integer_of_rational_of_two_rpow_integer
  · exact rational_of_two_three_a_rpow_rational_of_monomial_injective
      ha hmono h₂ h₃ haPow
  · exact h₂

/-- If `a` has a prime factor other than `2` and `3`, rationality of `a ^ x` together
with integrality at `2` and `3` forces `x` to be an integer. -/
theorem integer_of_two_three_a_rpow_rational_of_prime_factor
    {a p : ℕ} (ha : 0 < a) (hp : p.Prime) (hpa : p ∣ a)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (haPow : ∃ q : ℚ, (q : ℝ) = (a : ℝ) ^ x) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  have ha1 : 1 < a := hp.one_lt.trans_le (Nat.le_of_dvd ha hpa)
  exact integer_of_two_three_a_rpow_rational_of_monomial_injective ha1
    (monomial_injective_of_prime_dvd_ne_two_three ha hp hpa hp2 hp3)
    h₂ h₃ haPow

/-- Under a nonintegral exponent with integral powers at `2` and `3`, every positive
natural base having a rational `x`-th power is a product of powers of `2` and `3`. -/
theorem eq_two_pow_mul_three_pow_of_not_integer_of_rpows_rational
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    {a : ℕ} (ha : 0 < a)
    (haPow : ∃ q : ℚ, (q : ℝ) = (a : ℝ) ^ x) :
    ∃ u v : ℕ, a = 2 ^ u * 3 ^ v := by
  rw [← Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow ha]
  intro p hp hpa
  by_contra hp23
  have hp2 : p ≠ 2 := fun h ↦ hp23 (Or.inl h)
  have hp3 : p ≠ 3 := fun h ↦ hp23 (Or.inr h)
  exact hx (integer_of_two_three_a_rpow_rational_of_prime_factor
    ha hp hpa hp2 hp3 h₂ h₃ haPow)

/-- Exact classification under a hypothetical nonintegral two-base solution: the positive
natural bases with rational `x`-th power are precisely the products `2 ^ u * 3 ^ v`. -/
theorem rpow_rational_iff_eq_two_pow_mul_three_pow_of_not_integer
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    {a : ℕ} (ha : 0 < a) :
    (∃ q : ℚ, (q : ℝ) = (a : ℝ) ^ x) ↔
      ∃ u v : ℕ, a = 2 ^ u * 3 ^ v := by
  constructor
  · exact eq_two_pow_mul_three_pow_of_not_integer_of_rpows_rational
      hx h₂ h₃ ha
  · rintro ⟨u, v, rfl⟩
    obtain ⟨z₂, hz₂⟩ := h₂
    obtain ⟨z₃, hz₃⟩ := h₃
    refine ⟨((z₂ ^ u * z₃ ^ v : ℤ) : ℚ), ?_⟩
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) x u,
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) x v]
    rw [← hz₂, ← hz₃]

/-- Predicate-packaged form of the rational-base classification. -/
theorem TwoBaseNonintegerSolution.rpow_rational_iff_eq_two_pow_mul_three_pow
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {a : ℕ} (ha : 0 < a) :
    (∃ q : ℚ, (q : ℝ) = (a : ℝ) ^ x) ↔
      ∃ u v : ℕ, a = 2 ^ u * 3 ^ v :=
  rpow_rational_iff_eq_two_pow_mul_three_pow_of_not_integer
    hx.2 hx.1.1 hx.1.2 ha

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
