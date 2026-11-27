import GRHArticle.SingularModuli.RationalComplexEnclosure
import GRHArticle.SingularModuli.ClassPolynomialConstants
import GRHArticle.SingularModuli.ReducedForms

/-!
# The actual q-parameters of the two quartic class polynomials
-/

namespace GRHArticle.SingularModuli

open Real
open scoped BigOperators

private def sqrtInterval (n : ℕ) : RationalInterval :=
  let lo := Nat.sqrt (n * 10 ^ 100)
  ⟨(lo : ℚ) / 10 ^ 50, ((lo + 1 : ℕ) : ℚ) / 10 ^ 50⟩

private theorem contains_sqrtInterval (n : ℕ) : (sqrtInterval n).Contains √(n : ℝ) := by
  let k := Nat.sqrt (n * 10 ^ 100)
  have hlo : k ^ 2 ≤ n * 10 ^ 100 := Nat.sqrt_le' _
  have hhi : n * 10 ^ 100 < (k + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hcastlo : (k : ℝ) ^ 2 ≤ (n : ℝ) * 10 ^ 100 := by exact_mod_cast hlo
  have hcasthi : (n : ℝ) * 10 ^ 100 ≤ ((k : ℝ) + 1) ^ 2 := by exact_mod_cast hhi.le
  change (((k : ℚ) / 10 ^ 50 : ℚ) : ℝ) ≤ √(n : ℝ) ∧
    √(n : ℝ) ≤ (((((k + 1 : ℕ) : ℚ) / 10 ^ 50 : ℚ) : ℝ))
  push_cast
  have hnorm : (10 : ℝ) ^ 100 = (10 ^ 50) ^ 2 := by rw [← pow_mul]
  rw [hnorm] at hcastlo hcasthi
  constructor
  · apply Real.le_sqrt_of_sq_le
    rw [div_pow, div_le_iff₀ (by positivity)]
    exact hcastlo
  · apply (Real.sqrt_le_left (by positivity)).2
    rw [div_pow, le_div_iff₀ (by positivity)]
    exact hcasthi

private def piInterval : RationalInterval := ⟨piLower, piUpper⟩

private def expStep (A : RationalInterval) (n : ℕ) (U : RationalInterval) : RationalInterval :=
  (RationalInterval.point 1).add ((A.mul (RationalInterval.point (1 / (n : ℚ)))).mul U)

private def expApprox (A : RationalInterval) : ℕ → RationalInterval → RationalInterval
  | 0, U => U
  | n + 1, U => expApprox A n (expStep A (n + 1) U)

private theorem contains_expApprox {A U : RationalInterval} {x u : ℝ}
    (hx : A.Contains x) (hu : U.Contains u) (n : ℕ) :
    (expApprox A n U).Contains (Real.expNear n x u) := by
  induction n generalizing U u with
  | zero => simpa only [expApprox, Real.expNear_zero] using hu
  | succ n ih =>
    rw [expApprox, Real.expNear_succ]
    apply ih
    have hrat := RationalInterval.contains_point (1 / (n + 1 : ℕ))
    have hstep := RationalInterval.contains_add (RationalInterval.contains_point 1)
      (RationalInterval.contains_mul (RationalInterval.contains_mul hx hrat) hu)
    simpa only [expStep, Rat.cast_one, div_eq_mul_inv, one_mul, Rat.cast_inv, Rat.cast_add, Rat.cast_natCast,
      Nat.cast_add, Nat.cast_one] using hstep

private def expInterval (A : RationalInterval) : RationalInterval :=
  (expApprox A 48 (RationalInterval.point 0)).widen (2 / (Nat.factorial 48 : ℚ))

private theorem contains_expInterval {A : RationalInterval} {x : ℝ}
    (hx : A.Contains x) (hsmall : |x| ≤ 1) : (expInterval A).Contains (exp x) := by
  apply RationalInterval.contains_widen
    (contains_expApprox hx (by simpa only [Rat.cast_zero] using RationalInterval.contains_point 0) 48)
  have h := Real.exp_bound (n := 48) hsmall (by decide)
  rw [show Real.expNear 48 x 0 = ∑ m ∈ Finset.range 48, x ^ m / m.factorial by
    simp only [Real.expNear, mul_zero, add_zero]]
  refine h.trans ?_
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast]
  have hpow : |x| ^ 48 ≤ (1 : ℝ) := pow_le_one₀ (abs_nonneg x) hsmall
  refine (mul_le_mul_of_nonneg_right hpow (by positivity)).trans ?_
  rw [one_mul]
  norm_num [Nat.factorial]

private def qRadiusInterval (D a : ℕ+) : RationalInterval :=
  (expInterval ((piInterval.mul (sqrtInterval D)).mul
    (RationalInterval.point (-1 / (32 * ((a : ℕ) : ℚ)))))).pow 32

private theorem contains_qRadiusInterval (D a : ℕ+) (hD : (D : ℕ) ≤ 68) :
    (qRadiusInterval D a).Contains (exp (-(π * √(D : ℝ) / a))) := by
  let x := -(π * √(D : ℝ)) / (32 * (a : ℝ))
  have ha : 1 ≤ (a : ℝ) := by exact_mod_cast a.pos
  have hA : ((piInterval.mul (sqrtInterval D)).mul
      (RationalInterval.point (-1 / (32 * ((a : ℕ) : ℚ))))).Contains x := by
    have hs := contains_sqrtInterval (D : ℕ)
    have h := RationalInterval.contains_mul
      (RationalInterval.contains_mul (show piInterval.Contains π from piLower_le_pi_le_piUpper) hs)
      (RationalInterval.contains_point (-1 / (32 * ((a : ℕ) : ℚ))))
    convert h using 1
    dsimp only [x]
    push_cast
    ring
  have hx : |x| ≤ 1 := by
    have hD' : (D : ℝ) ≤ 68 := by exact_mod_cast hD
    have hs : √(D : ℝ) ≤ 9 := (Real.sqrt_le_left (by norm_num)).mpr (by linarith only [hD'])
    have hπ : π ≤ (7 : ℝ) / 2 := by linarith only [Real.pi_lt_d2]
    have hmul := mul_le_mul hπ hs (sqrt_nonneg _) (by norm_num : 0 ≤ (7 : ℝ) / 2)
    dsimp only [x]
    rw [abs_div, abs_neg, abs_of_nonneg (mul_nonneg Real.pi_pos.le (sqrt_nonneg _)),
      abs_of_pos (by positivity)]
    exact (div_le_one (by positivity)).2 (by linarith only [hmul, ha])
  have h := RationalInterval.contains_pow (contains_expInterval hA hx) 32
  rw [← Real.exp_nat_mul] at h
  norm_num only [Nat.cast_ofNat] at h
  have he : (32 : ℝ) * x = -(π * √(D : ℝ) / a) := by dsimp only [x]; ring
  rw [he] at h
  exact h

private noncomputable def polarPhase (a : ℕ+) (b : ℤ) : ℂ :=
  ⟨Real.cos (-π * (b : ℝ) / a), Real.sin (-π * (b : ℝ) / a)⟩

private theorem qParam_quadraticPoint_polar (D a : ℕ+) (b : ℤ) :
    Function.Periodic.qParam 1 (quadraticPoint D a b) =
      (exp (-(π * √(D : ℝ) / a)) : ℂ) * polarPhase a b := by
  have h : (2 : ℂ) * π * Complex.I * (quadraticPoint D a b : ℂ) /
      ((1 : ℝ) : ℂ) = (-(π * √(D : ℝ) / a) : ℝ) + ((-π * (b : ℝ) / a) : ℝ) * Complex.I := by
    apply Complex.ext <;> simp [quadraticPoint, Complex.mul_re, Complex.mul_im]
    all_goals field_simp
  rw [Function.Periodic.qParam, h, Complex.exp_add_mul_I, ← Complex.ofReal_exp]
  congr 1
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Complex.ext <;> simp only [polarPhase, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_add, add_zero, sub_zero]

private theorem contains_phase_point {a : ℕ+} {b : ℤ} {r i : ℚ}
    (hr : Real.cos (-π * (b : ℝ) / a) = (r : ℝ))
    (hi : Real.sin (-π * (b : ℝ) / a) = (i : ℝ)) :
    (RationalComplexBox.point r i).Contains (polarPhase a b) := by
  rw [polarPhase, hr, hi]
  exact RationalComplexBox.contains_point r i

/-- The four reduced representatives for discriminant -55, in certificate order. -/
def quartic55Form : Fin 4 → FormCoefficients :=
  ![⟨1, 1, 14⟩, ⟨2, -1, 7⟩, ⟨2, 1, 7⟩, ⟨4, 3, 4⟩]

/-- The four reduced representatives for discriminant -68, in certificate order. -/
def quartic68Form : Fin 4 → FormCoefficients :=
  ![⟨1, 0, 17⟩, ⟨2, 2, 9⟩, ⟨3, -2, 6⟩, ⟨3, 2, 6⟩]

private def phaseBox55 : Fin 4 → RationalComplexBox :=
  let s := (sqrtInterval 2).mul (RationalInterval.point (-1 / 2))
  ![RationalComplexBox.point (-1) 0, RationalComplexBox.point 0 1,
    RationalComplexBox.point 0 (-1), ⟨s, s⟩]

private def phaseBox68 : Fin 4 → RationalComplexBox :=
  let s := (sqrtInterval 3).mul (RationalInterval.point (1 / 2))
  ![RationalComplexBox.point 1 0, RationalComplexBox.point (-1) 0,
    ⟨RationalInterval.point (-1 / 2), s⟩, ⟨RationalInterval.point (-1 / 2), s.neg⟩]

private theorem contains_phaseBox55 (i : Fin 4) :
    (phaseBox55 i).Contains (polarPhase (quartic55Form i).a (quartic55Form i).b) := by
  fin_cases i
  · change (RationalComplexBox.point (-1) 0).Contains (polarPhase 1 1)
    have he : -π * ((1 : ℤ) : ℝ) / ((1 : ℕ+) : ℝ) = -π := by push_cast; ring
    apply contains_phase_point <;> rw [he] <;> norm_num [Real.cos_neg, Real.sin_neg]
  · change (RationalComplexBox.point 0 1).Contains (polarPhase 2 (-1))
    have he : -π * ((-1 : ℤ) : ℝ) / ((2 : ℕ+) : ℝ) = π / 2 := by push_cast; ring
    apply contains_phase_point <;> rw [he] <;> norm_num
  · change (RationalComplexBox.point 0 (-1)).Contains (polarPhase 2 1)
    have he : -π * ((1 : ℤ) : ℝ) / ((2 : ℕ+) : ℝ) = -(π / 2) := by push_cast; ring
    apply contains_phase_point <;> rw [he] <;> norm_num [Real.cos_neg, Real.sin_neg]
  · let s := (sqrtInterval 2).mul (RationalInterval.point (-1 / 2))
    change s.Contains (Real.cos (-π * (3 : ℝ) / 4)) ∧
      s.Contains (Real.sin (-π * (3 : ℝ) / 4))
    rw [show -π * (3 : ℝ) / 4 = -(π - π / 4) by ring, Real.cos_neg, Real.sin_neg, Real.cos_pi_sub,
      Real.sin_pi_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
    have h := RationalInterval.contains_mul (contains_sqrtInterval 2)
      (RationalInterval.contains_point (-1 / 2))
    have he : √(2 : ℝ) * ((-1 / 2 : ℚ) : ℝ) = -(√(2 : ℝ) / 2) := by push_cast; ring
    rw [Nat.cast_ofNat, he] at h
    exact ⟨h, h⟩

private theorem contains_phaseBox68 (i : Fin 4) :
    (phaseBox68 i).Contains (polarPhase (quartic68Form i).a (quartic68Form i).b) := by
  fin_cases i
  · change (RationalComplexBox.point 1 0).Contains (polarPhase 1 0)
    have he : -π * ((0 : ℤ) : ℝ) / ((1 : ℕ+) : ℝ) = 0 := by simp
    apply contains_phase_point <;> rw [he] <;> norm_num
  · change (RationalComplexBox.point (-1) 0).Contains (polarPhase 2 2)
    have he : -π * ((2 : ℤ) : ℝ) / ((2 : ℕ+) : ℝ) = -π := by push_cast; ring
    apply contains_phase_point <;> rw [he] <;> norm_num [Real.cos_neg, Real.sin_neg]
  · let s := (sqrtInterval 3).mul (RationalInterval.point (1 / 2))
    change (RationalInterval.point (-1 / 2)).Contains (Real.cos (-π * ((-2 : ℤ) : ℝ) / 3)) ∧
      s.Contains (Real.sin (-π * ((-2 : ℤ) : ℝ) / 3))
    rw [show -π * ((-2 : ℤ) : ℝ) / 3 = π - π / 3 by push_cast; ring, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    have h := RationalInterval.contains_mul (contains_sqrtInterval 3)
      (RationalInterval.contains_point (1 / 2))
    have he : √(3 : ℝ) * ((1 / 2 : ℚ) : ℝ) = √(3 : ℝ) / 2 := by push_cast; ring
    rw [Nat.cast_ofNat, he] at h
    exact ⟨by simpa [div_eq_mul_inv] using RationalInterval.contains_point (-1 / 2), h⟩
  · let s := (sqrtInterval 3).mul (RationalInterval.point (1 / 2))
    change (RationalInterval.point (-1 / 2)).Contains (Real.cos (-π * (2 : ℝ) / 3)) ∧
      s.neg.Contains (Real.sin (-π * (2 : ℝ) / 3))
    rw [show -π * (2 : ℝ) / 3 = -(π - π / 3) by ring, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
    have h := RationalInterval.contains_mul (contains_sqrtInterval 3)
      (RationalInterval.contains_point (1 / 2))
    have he : √(3 : ℝ) * ((1 / 2 : ℚ) : ℝ) = √(3 : ℝ) / 2 := by push_cast; ring
    rw [Nat.cast_ofNat, he] at h
    exact ⟨by simpa [div_eq_mul_inv] using RationalInterval.contains_point (-1 / 2), RationalInterval.contains_neg h⟩

def quartic55QBox (i : Fin 4) : RationalComplexBox :=
  (RationalComplexBox.real (qRadiusInterval 55 (quartic55Form i).a)).mul (phaseBox55 i)

def quartic68QBox (i : Fin 4) : RationalComplexBox :=
  (RationalComplexBox.real (qRadiusInterval 68 (quartic68Form i).a)).mul (phaseBox68 i)

/-- The rational box contains the actual q-parameter at every -55 input. -/
theorem quartic55QBox_contains (i : Fin 4) : (quartic55QBox i).Contains
    (Function.Periodic.qParam 1 (quadraticPoint 55 (quartic55Form i).a (quartic55Form i).b)) := by
  rw [qParam_quadraticPoint_polar]
  exact RationalComplexBox.contains_mul
    (RationalComplexBox.contains_real (contains_qRadiusInterval 55 _ (by decide)))
    (contains_phaseBox55 i)

/-- The rational box contains the actual q-parameter at every -68 input. -/
theorem quartic68QBox_contains (i : Fin 4) : (quartic68QBox i).Contains
    (Function.Periodic.qParam 1 (quadraticPoint 68 (quartic68Form i).a (quartic68Form i).b)) := by
  rw [qParam_quadraticPoint_polar]
  exact RationalComplexBox.contains_mul
    (RationalComplexBox.contains_real (contains_qRadiusInterval 68 _ (by decide)))
    (contains_phaseBox68 i)

end GRHArticle.SingularModuli
