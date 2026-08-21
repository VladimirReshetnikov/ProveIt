import ExponentialIdentities.TwoBaseIntegerExponent.RationalThirdBase
import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicIntegerDeterminant
import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicOutputBridge

/-!
# Algebraic output at a third natural base

This module proves the three-base interpolation determinant theorem first for an
explicit algebraic integer in a number field, then for every real output algebraic
over `ℚ` by clearing a common natural denominator.
-/

open scoped BigOperators Nat

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

private abbrev AlgebraicRowBox (n : ℕ) :=
  Fin (n * n) × Fin (n * n) × Fin (n * n)

private abbrev AlgebraicColBox (n : ℕ) :=
  Fin ((n * n) * n) × Fin ((n * n) * n)

private theorem card_algebraicRowBox (n : ℕ) :
    Fintype.card (AlgebraicRowBox n) = n ^ 6 := by
  simp [AlgebraicRowBox]
  ring

private theorem card_algebraicColBox (n : ℕ) :
    Fintype.card (AlgebraicColBox n) = n ^ 6 := by
  simp [AlgebraicColBox]
  ring

private def algebraicRowNat (a : ℕ) {n : ℕ} (i : AlgebraicRowBox n) : ℕ :=
  2 ^ (i.1 : ℕ) * 3 ^ (i.2.1 : ℕ) * a ^ (i.2.2 : ℕ)

private def algebraicRowArg (a : ℕ) {n : ℕ} (i : AlgebraicRowBox n) : ℝ :=
  Real.log (algebraicRowNat a i : ℝ)

private def algebraicColArg {n : ℕ} (x : ℝ) (j : AlgebraicColBox n) : ℝ :=
  (j.1 : ℝ) + (j.2 : ℝ) * x

private theorem algebraicRowNat_injective {a n : ℕ}
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2.1 * a ^ u.2.2)) :
    Function.Injective (@algebraicRowNat a n) := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  have huv : ((i : ℕ), (j : ℕ), (k : ℕ)) =
      ((i' : ℕ), (j' : ℕ), (k' : ℕ)) := hmono h
  simp only [Prod.mk.injEq] at huv
  exact Prod.ext (Fin.ext huv.1) (Prod.ext (Fin.ext huv.2.1) (Fin.ext huv.2.2))

private theorem algebraicColArg_injective {x : ℝ} (hx : Irrational x) (n : ℕ) :
    Function.Injective (@algebraicColArg n x) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have huv : ((i : ℕ), (j : ℕ)) = ((i' : ℕ), (j' : ℕ)) :=
    IntegerExponent.Irrational.injective_nat_add_mul hx h
  simp only [Prod.mk.injEq] at huv
  exact Prod.ext (Fin.ext huv.1) (Fin.ext huv.2)

private theorem algebraicRowNat_pos {a n : ℕ} (ha : 0 < a)
    (i : AlgebraicRowBox n) : 0 < algebraicRowNat a i := by
  unfold algebraicRowNat
  positivity

private theorem algebraicRowArg_injective {a : ℕ} (ha : 0 < a)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2.1 * a ^ u.2.2))
    (n : ℕ) : Function.Injective (@algebraicRowArg a n) := by
  intro i j h
  apply algebraicRowNat_injective hmono
  have hc : (algebraicRowNat a i : ℝ) = (algebraicRowNat a j : ℝ) :=
    Real.log_injOn_pos
      (show 0 < (algebraicRowNat a i : ℝ) by
        exact_mod_cast algebraicRowNat_pos ha i)
      (show 0 < (algebraicRowNat a j : ℝ) by
        exact_mod_cast algebraicRowNat_pos ha j) h
  exact Nat.cast_injective hc

private theorem algebraicRowArg_nonneg {a n : ℕ} (ha : 0 < a)
    (i : AlgebraicRowBox n) : 0 ≤ algebraicRowArg a i := by
  apply Real.log_nonneg
  exact_mod_cast algebraicRowNat_pos ha i

private theorem algebraicRowArg_le {a n : ℕ} (ha : 1 ≤ a)
    (i : AlgebraicRowBox n) :
    algebraicRowArg a i ≤
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
  have hexpand : algebraicRowArg a i =
      ((i.1 : ℕ) : ℝ) * Real.log 2 +
      ((i.2.1 : ℕ) : ℝ) * Real.log 3 +
      ((i.2.2 : ℕ) : ℝ) * Real.log a := by
    simp only [algebraicRowArg, algebraicRowNat, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
  rw [hexpand]
  linarith

private theorem algebraicColArg_nonneg {n : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (j : AlgebraicColBox n) : 0 ≤ algebraicColArg x j := by
  dsimp only [algebraicColArg]
  positivity

private theorem algebraicColArg_le {n : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (j : AlgebraicColBox n) :
    algebraicColArg x j ≤ ((n * n) * n : ℕ) * (1 + x) := by
  have hv₀ : ((j.1 : ℕ) : ℝ) ≤ ((n * n) * n : ℕ) := by
    exact_mod_cast j.1.isLt.le
  have hv₁ : ((j.2 : ℕ) : ℝ) ≤ ((n * n) * n : ℕ) := by
    exact_mod_cast j.2.isLt.le
  have hv₁x : ((j.2 : ℕ) : ℝ) * x ≤
      (((n * n) * n : ℕ) : ℝ) * x := mul_le_mul_of_nonneg_right hv₁ hx
  dsimp only [algebraicColArg]
  linarith

private theorem algebraic_abs_rowArg_mul_colArg_le {a n D : ℕ} {x : ℝ}
    (ha : 1 < a) (hx : 0 ≤ x)
    (hD : (Real.log 2 + Real.log 3 + Real.log a) * (1 + x) ≤ D)
    (i : AlgebraicRowBox n) (j : AlgebraicColBox n) :
    |algebraicRowArg a i * algebraicColArg x j| ≤ (D * n ^ 5 : ℕ) := by
  have hrow0 := algebraicRowArg_nonneg (by omega : 0 < a) i
  have hcol0 := algebraicColArg_nonneg hx j
  have hrow := algebraicRowArg_le ha.le i
  have hcol := algebraicColArg_le hx j
  rw [abs_of_nonneg (mul_nonneg hrow0 hcol0)]
  calc
    algebraicRowArg a i * algebraicColArg x j ≤
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

private def algebraicEntry {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K) (zTwo zThree : ℤ)
    {n : ℕ} (a : ℕ) (i : AlgebraicRowBox n) (j : AlgebraicColBox n) :
    NumberField.RingOfIntegers K :=
  (2 : NumberField.RingOfIntegers K) ^ ((i.1 : ℕ) * (j.1 : ℕ)) *
    (3 : NumberField.RingOfIntegers K) ^ ((i.2.1 : ℕ) * (j.1 : ℕ)) *
    (a : NumberField.RingOfIntegers K) ^ ((i.2.2 : ℕ) * (j.1 : ℕ)) *
    (zTwo : NumberField.RingOfIntegers K) ^ ((i.1 : ℕ) * (j.2 : ℕ)) *
    (zThree : NumberField.RingOfIntegers K) ^ ((i.2.1 : ℕ) * (j.2 : ℕ)) *
    alpha ^ ((i.2.2 : ℕ) * (j.2 : ℕ))

private def scaledAlgebraicEntry {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K) (scale L : ℕ) (zTwo zThree : ℤ)
    {n : ℕ} (a : ℕ) (i : AlgebraicRowBox n) (j : AlgebraicColBox n) :
    NumberField.RingOfIntegers K :=
  (scale : NumberField.RingOfIntegers K) ^
      (L - (i.2.2 : ℕ) * (j.2 : ℕ)) *
    algebraicEntry alpha zTwo zThree a i j

private theorem algebraic_exp_log_mul_nat_add_eq {R : ℕ} (hR : 0 < R)
    {x : ℝ} (vZero vOne : ℕ) :
    Real.exp (Real.log (R : ℝ) * ((vZero : ℝ) + (vOne : ℝ) * x)) =
      (R : ℝ) ^ vZero * ((R : ℝ) ^ x) ^ vOne := by
  rw [← Real.rpow_def_of_pos (by exact_mod_cast hR)]
  rw [Real.rpow_add (by exact_mod_cast hR)]
  rw [Real.rpow_natCast]
  rw [show (vOne : ℝ) * x = x * (vOne : ℝ) by ring]
  rw [Real.rpow_mul_natCast (by exact_mod_cast hR.le)]

private theorem algebraicProduct_rpow_eq {a : ℕ} (ha : 0 < a)
    {x : ℝ} {zTwo zThree : ℤ}
    (hTwo : (zTwo : ℝ) = (2 : ℝ) ^ x)
    (hThree : (zThree : ℝ) = (3 : ℝ) ^ x)
    (uTwo uThree ua : ℕ) :
    (((2 ^ uTwo * 3 ^ uThree * a ^ ua : ℕ) : ℝ) ^ x) =
      (zTwo : ℝ) ^ uTwo * (zThree : ℝ) ^ uThree *
        ((a : ℝ) ^ x) ^ ua := by
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) x uTwo,
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) x uThree,
    ← Real.rpow_pow_comm (by exact_mod_cast ha.le) x ua]
  rw [← hTwo, ← hThree]

private theorem algebraic_exp_entry_real {a n : ℕ} (ha : 0 < a)
    {x : ℝ} {zTwo zThree : ℤ}
    (hTwo : (zTwo : ℝ) = (2 : ℝ) ^ x)
    (hThree : (zThree : ℝ) = (3 : ℝ) ^ x)
    (i : AlgebraicRowBox n) (j : AlgebraicColBox n) :
    Real.exp (algebraicRowArg a i * algebraicColArg x j) =
      (2 : ℝ) ^ ((i.1 : ℕ) * (j.1 : ℕ)) *
      (3 : ℝ) ^ ((i.2.1 : ℕ) * (j.1 : ℕ)) *
      (a : ℝ) ^ ((i.2.2 : ℕ) * (j.1 : ℕ)) *
      (zTwo : ℝ) ^ ((i.1 : ℕ) * (j.2 : ℕ)) *
      (zThree : ℝ) ^ ((i.2.1 : ℕ) * (j.2 : ℕ)) *
      ((a : ℝ) ^ x) ^ ((i.2.2 : ℕ) * (j.2 : ℕ)) := by
  rw [algebraicRowArg, algebraicColArg,
    algebraic_exp_log_mul_nat_add_eq (algebraicRowNat_pos ha i)]
  rw [show algebraicRowNat a i =
    2 ^ (i.1 : ℕ) * 3 ^ (i.2.1 : ℕ) * a ^ (i.2.2 : ℕ) by rfl]
  rw [algebraicProduct_rpow_eq ha hTwo hThree]
  push_cast
  simp only [mul_pow, ← pow_mul]
  ring

private theorem map_algebraicEntry_eq_exp
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K) (sigma : K →+* ℂ)
    {a n : ℕ} (ha : 0 < a) {x : ℝ} {zTwo zThree : ℤ}
    (hTwo : (zTwo : ℝ) = (2 : ℝ) ^ x)
    (hThree : (zThree : ℝ) = (3 : ℝ) ^ x)
    (haPow : sigma (alpha : K) = (((a : ℝ) ^ x : ℝ) : ℂ))
    (i : AlgebraicRowBox n) (j : AlgebraicColBox n) :
    sigma ((algebraicEntry alpha zTwo zThree a i j :
      NumberField.RingOfIntegers K) : K) =
      (Real.exp (algebraicRowArg a i * algebraicColArg x j) : ℂ) := by
  rw [algebraic_exp_entry_real ha hTwo hThree]
  simp only [algebraicEntry, map_mul, map_pow, map_natCast, map_intCast]
  have hsigmaTwo : sigma ((algebraMap (NumberField.RingOfIntegers K) K) 2) =
      (2 : ℂ) := by rw [map_ofNat, map_ofNat]
  have hsigmaThree : sigma ((algebraMap (NumberField.RingOfIntegers K) K) 3) =
      (3 : ℂ) := by rw [map_ofNat, map_ofNat]
  rw [hsigmaTwo, hsigmaThree, haPow]
  push_cast
  ring

private theorem map_scaledAlgebraicEntry_eq_smul_exp
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K) (sigma : K →+* ℂ)
    {a n scale L : ℕ} (ha : 0 < a) {x : ℝ} {zTwo zThree : ℤ}
    (hTwo : (zTwo : ℝ) = (2 : ℝ) ^ x)
    (hThree : (zThree : ℝ) = (3 : ℝ) ^ x)
    (haPow : sigma (alpha : K) =
      (scale : ℂ) * (((a : ℝ) ^ x : ℝ) : ℂ))
    (i : AlgebraicRowBox n) (j : AlgebraicColBox n)
    (he : (i.2.2 : ℕ) * (j.2 : ℕ) ≤ L) :
    sigma ((scaledAlgebraicEntry alpha scale L zTwo zThree a i j :
      NumberField.RingOfIntegers K) : K) =
      (scale : ℂ) ^ L *
        (Real.exp (algebraicRowArg a i * algebraicColArg x j) : ℂ) := by
  rw [algebraic_exp_entry_real ha hTwo hThree]
  simp only [scaledAlgebraicEntry, algebraicEntry, map_mul, map_pow, map_natCast,
    map_intCast]
  have hsigmaTwo : sigma ((algebraMap (NumberField.RingOfIntegers K) K) 2) =
      (2 : ℂ) := by rw [map_ofNat, map_ofNat]
  have hsigmaThree : sigma ((algebraMap (NumberField.RingOfIntegers K) K) 3) =
      (3 : ℂ) := by rw [map_ofNat, map_ofNat]
  rw [hsigmaTwo, hsigmaThree, haPow, mul_pow]
  push_cast
  have hscale :
      (scale : ℂ) ^ ((i.2.2 : ℕ) * (j.2 : ℕ)) *
          (scale : ℂ) ^ (L - (i.2.2 : ℕ) * (j.2 : ℕ)) =
        (scale : ℂ) ^ L := by
    rw [← pow_add, Nat.add_sub_of_le he]
  rw [← hscale]
  ring

private theorem algebraic_coordinate_mul_le {n : ℕ}
    (u : Fin (n * n)) (v : Fin ((n * n) * n)) :
    (u : ℕ) * (v : ℕ) ≤ n ^ 5 := by
  calc
    (u : ℕ) * (v : ℕ) ≤ (n * n) * ((n * n) * n) :=
      Nat.mul_le_mul u.isLt.le v.isLt.le
    _ = n ^ 5 := by ring

private theorem norm_embedding_natCast
    {K : Type*} [Field K] [NumberField K] (tau : K →+* ℂ) (q : ℕ) :
    ‖tau (((q : NumberField.RingOfIntegers K) : K))‖ = (q : ℝ) := by
  rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_natCast, map_natCast]
  exact Complex.norm_natCast q

private theorem norm_embedding_intCast
    {K : Type*} [Field K] [NumberField K] (tau : K →+* ℂ) (z : ℤ) :
    ‖tau (((z : NumberField.RingOfIntegers K) : K))‖ = |(z : ℝ)| := by
  rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_intCast, map_intCast]
  exact Complex.norm_intCast z

private theorem norm_pow_le_uniform_pow
    {z : ℂ} {T : ℝ} {e L : ℕ} (hT : 1 ≤ T)
    (hz : ‖z‖ ≤ T) (he : e ≤ L) :
    ‖z ^ e‖ ≤ T ^ L := by
  rw [norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _) hz e).trans (pow_le_pow_right₀ hT he)

private theorem norm_pow_mul_complementary_pow_le
    {z w : ℂ} {T : ℝ} {e L : ℕ}
    (hz : ‖z‖ ≤ T) (hw : ‖w‖ ≤ T) (he : e ≤ L) :
    ‖z ^ e * w ^ (L - e)‖ ≤ T ^ L := by
  rw [norm_mul, norm_pow, norm_pow]
  calc
    ‖z‖ ^ e * ‖w‖ ^ (L - e) ≤ T ^ e * T ^ (L - e) := by
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz _)
        (pow_le_pow_left₀ (norm_nonneg _) hw _) (pow_nonneg (norm_nonneg _) _)
        (pow_nonneg (le_trans (norm_nonneg _) hw) _)
    _ = T ^ (e + (L - e)) := (pow_add T e (L - e)).symm
    _ = T ^ L := by rw [Nat.add_sub_of_le he]

private theorem norm_map_algebraicEntry_le
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K) (zTwo zThree : ℤ)
    {a n T : ℕ}
    (hTOne : (1 : ℝ) ≤ T) (hTTwo : (2 : ℝ) ≤ T)
    (hTThree : (3 : ℝ) ≤ T) (hTa : (a : ℝ) ≤ T)
    (hTzTwo : |(zTwo : ℝ)| ≤ T) (hTzThree : |(zThree : ℝ)| ≤ T)
    (hTalpha : NumberField.house (alpha : K) ≤ T)
    (tau : K →+* ℂ) (i : AlgebraicRowBox n) (j : AlgebraicColBox n) :
    ‖tau ((algebraicEntry alpha zTwo zThree a i j :
      NumberField.RingOfIntegers K) : K)‖ ≤ (T : ℝ) ^ (6 * n ^ 5) := by
  have hAlpha : ‖tau (alpha : K)‖ ≤ (T : ℝ) :=
    (NumberField.norm_embedding_le_house (alpha : K) tau).trans hTalpha
  have heTwo := algebraic_coordinate_mul_le i.1 j.1
  have heThree := algebraic_coordinate_mul_le i.2.1 j.1
  have hea := algebraic_coordinate_mul_le i.2.2 j.1
  have hezTwo := algebraic_coordinate_mul_le i.1 j.2
  have hezThree := algebraic_coordinate_mul_le i.2.1 j.2
  have heAlpha := algebraic_coordinate_mul_le i.2.2 j.2
  have hExp :
      (i.1 : ℕ) * (j.1 : ℕ) + (i.2.1 : ℕ) * (j.1 : ℕ) +
        (i.2.2 : ℕ) * (j.1 : ℕ) + (i.1 : ℕ) * (j.2 : ℕ) +
        (i.2.1 : ℕ) * (j.2 : ℕ) + (i.2.2 : ℕ) * (j.2 : ℕ) ≤
        6 * n ^ 5 := by omega
  simp only [algebraicEntry, map_mul, map_pow, norm_mul, norm_pow]
  calc
    ‖tau (((2 : NumberField.RingOfIntegers K) : K))‖ ^ ((i.1 : ℕ) * (j.1 : ℕ)) *
          ‖tau (((3 : NumberField.RingOfIntegers K) : K))‖ ^ ((i.2.1 : ℕ) * (j.1 : ℕ)) *
          ‖tau (((a : NumberField.RingOfIntegers K) : K))‖ ^ ((i.2.2 : ℕ) * (j.1 : ℕ)) *
          ‖tau (((zTwo : NumberField.RingOfIntegers K) : K))‖ ^ ((i.1 : ℕ) * (j.2 : ℕ)) *
          ‖tau (((zThree : NumberField.RingOfIntegers K) : K))‖ ^ ((i.2.1 : ℕ) * (j.2 : ℕ)) *
          ‖tau (alpha : K)‖ ^ ((i.2.2 : ℕ) * (j.2 : ℕ)) ≤
        (T : ℝ) ^ ((i.1 : ℕ) * (j.1 : ℕ)) *
          (T : ℝ) ^ ((i.2.1 : ℕ) * (j.1 : ℕ)) *
          (T : ℝ) ^ ((i.2.2 : ℕ) * (j.1 : ℕ)) *
          (T : ℝ) ^ ((i.1 : ℕ) * (j.2 : ℕ)) *
          (T : ℝ) ^ ((i.2.1 : ℕ) * (j.2 : ℕ)) *
          (T : ℝ) ^ ((i.2.2 : ℕ) * (j.2 : ℕ)) := by
      gcongr
      · calc
          ‖tau (2 : K)‖ = (2 : ℝ) := by rw [map_ofNat]; norm_num
          _ ≤ (T : ℝ) := hTTwo
      · calc
          ‖tau (3 : K)‖ = (3 : ℝ) := by rw [map_ofNat]; norm_num
          _ ≤ (T : ℝ) := hTThree
      · calc
          ‖tau (a : K)‖ = (a : ℝ) := by
            rw [map_natCast, Complex.norm_natCast]
          _ ≤ (T : ℝ) := hTa
      · calc
          ‖tau (zTwo : K)‖ = |(zTwo : ℝ)| := by
            rw [map_intCast, Complex.norm_intCast]
          _ ≤ (T : ℝ) := hTzTwo
      · calc
          ‖tau (zThree : K)‖ = |(zThree : ℝ)| := by
            rw [map_intCast, Complex.norm_intCast]
          _ ≤ (T : ℝ) := hTzThree
    _ = (T : ℝ) ^
        ((i.1 : ℕ) * (j.1 : ℕ) + (i.2.1 : ℕ) * (j.1 : ℕ) +
          (i.2.2 : ℕ) * (j.1 : ℕ) + (i.1 : ℕ) * (j.2 : ℕ) +
          (i.2.1 : ℕ) * (j.2 : ℕ) + (i.2.2 : ℕ) * (j.2 : ℕ)) := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    _ ≤ (T : ℝ) ^ (6 * n ^ 5) := pow_le_pow_right₀ hTOne hExp

private theorem norm_map_scaledAlgebraicEntry_le
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K) (scale : ℕ) (zTwo zThree : ℤ)
    {a n T : ℕ}
    (hTOne : (1 : ℝ) ≤ T) (hTTwo : (2 : ℝ) ≤ T)
    (hTThree : (3 : ℝ) ≤ T) (hTa : (a : ℝ) ≤ T)
    (hTzTwo : |(zTwo : ℝ)| ≤ T) (hTzThree : |(zThree : ℝ)| ≤ T)
    (hTscale : (scale : ℝ) ≤ T)
    (hTalpha : NumberField.house (alpha : K) ≤ T)
    (tau : K →+* ℂ) (i : AlgebraicRowBox n) (j : AlgebraicColBox n) :
    ‖tau ((scaledAlgebraicEntry alpha scale (n ^ 5) zTwo zThree a i j :
      NumberField.RingOfIntegers K) : K)‖ ≤ (T : ℝ) ^ (6 * n ^ 5) := by
  let eTwo := (i.1 : ℕ) * (j.1 : ℕ)
  let eThree := (i.2.1 : ℕ) * (j.1 : ℕ)
  let ea := (i.2.2 : ℕ) * (j.1 : ℕ)
  let ezTwo := (i.1 : ℕ) * (j.2 : ℕ)
  let ezThree := (i.2.1 : ℕ) * (j.2 : ℕ)
  let eAlpha := (i.2.2 : ℕ) * (j.2 : ℕ)
  have heTwo : eTwo ≤ n ^ 5 := algebraic_coordinate_mul_le i.1 j.1
  have heThree : eThree ≤ n ^ 5 := algebraic_coordinate_mul_le i.2.1 j.1
  have hea : ea ≤ n ^ 5 := algebraic_coordinate_mul_le i.2.2 j.1
  have hezTwo : ezTwo ≤ n ^ 5 := algebraic_coordinate_mul_le i.1 j.2
  have hezThree : ezThree ≤ n ^ 5 := algebraic_coordinate_mul_le i.2.1 j.2
  have heAlpha : eAlpha ≤ n ^ 5 := algebraic_coordinate_mul_le i.2.2 j.2
  have hAlpha : ‖tau (alpha : K)‖ ≤ (T : ℝ) :=
    (NumberField.norm_embedding_le_house (alpha : K) tau).trans hTalpha
  have hTwoNorm : ‖(2 : ℂ)‖ ≤ (T : ℝ) := by
    calc
      ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
      _ ≤ (T : ℝ) := hTTwo
  have hThreeNorm : ‖(3 : ℂ)‖ ≤ (T : ℝ) := by
    calc
      ‖(3 : ℂ)‖ = (3 : ℝ) := by norm_num
      _ ≤ (T : ℝ) := hTThree
  have haNorm : ‖(a : ℂ)‖ ≤ (T : ℝ) := by
    rw [Complex.norm_natCast]
    exact hTa
  have hzTwoNorm : ‖(zTwo : ℂ)‖ ≤ (T : ℝ) := by
    rw [Complex.norm_intCast]
    exact hTzTwo
  have hzThreeNorm : ‖(zThree : ℂ)‖ ≤ (T : ℝ) := by
    rw [Complex.norm_intCast]
    exact hTzThree
  have hScaleNorm : ‖(scale : ℂ)‖ ≤ (T : ℝ) := by
    rw [Complex.norm_natCast]
    exact hTscale
  have gTwo : ‖tau ((2 : K) ^ eTwo)‖ ≤ (T : ℝ) ^ (n ^ 5) := by
    simpa only [map_pow, map_ofNat] using
      (norm_pow_le_uniform_pow hTOne hTwoNorm heTwo)
  have gThree : ‖tau ((3 : K) ^ eThree)‖ ≤ (T : ℝ) ^ (n ^ 5) := by
    simpa only [map_pow, map_ofNat] using
      (norm_pow_le_uniform_pow hTOne hThreeNorm heThree)
  have ga : ‖tau ((a : K) ^ ea)‖ ≤ (T : ℝ) ^ (n ^ 5) := by
    simpa only [map_pow, map_natCast] using
      (norm_pow_le_uniform_pow hTOne haNorm hea)
  have gzTwo : ‖tau ((zTwo : K) ^ ezTwo)‖ ≤ (T : ℝ) ^ (n ^ 5) := by
    simpa only [map_pow, map_intCast] using
      (norm_pow_le_uniform_pow hTOne hzTwoNorm hezTwo)
  have gzThree : ‖tau ((zThree : K) ^ ezThree)‖ ≤ (T : ℝ) ^ (n ^ 5) := by
    simpa only [map_pow, map_intCast] using
      (norm_pow_le_uniform_pow hTOne hzThreeNorm hezThree)
  have gAlpha :
      ‖tau ((scale : K) ^ (n ^ 5 - eAlpha) * (alpha : K) ^ eAlpha)‖ ≤
        (T : ℝ) ^ (n ^ 5) := by
    rw [map_mul, map_pow, map_pow, mul_comm]
    simpa only [map_natCast] using
      (norm_pow_mul_complementary_pow_le hAlpha hScaleNorm heAlpha)
  have hrearrange :
      ‖tau ((scaledAlgebraicEntry alpha scale (n ^ 5) zTwo zThree a i j :
        NumberField.RingOfIntegers K) : K)‖ =
        ‖tau ((2 : K) ^ eTwo)‖ * ‖tau ((3 : K) ^ eThree)‖ *
          ‖tau ((a : K) ^ ea)‖ * ‖tau ((zTwo : K) ^ ezTwo)‖ *
          ‖tau ((zThree : K) ^ ezThree)‖ *
          ‖tau ((scale : K) ^ (n ^ 5 - eAlpha) * (alpha : K) ^ eAlpha)‖ := by
    simp only [scaledAlgebraicEntry, algebraicEntry, eTwo, eThree, ea, ezTwo,
      ezThree, eAlpha, map_mul, map_pow, norm_mul,
      NumberField.RingOfIntegers.coe_eq_algebraMap, map_natCast, map_intCast,
      map_ofNat]
    ring
  rw [hrearrange]
  calc
    ‖tau ((2 : K) ^ eTwo)‖ * ‖tau ((3 : K) ^ eThree)‖ *
          ‖tau ((a : K) ^ ea)‖ * ‖tau ((zTwo : K) ^ ezTwo)‖ *
          ‖tau ((zThree : K) ^ ezThree)‖ *
          ‖tau ((scale : K) ^ (n ^ 5 - eAlpha) * (alpha : K) ^ eAlpha)‖ ≤
        ((T : ℝ) ^ (n ^ 5)) ^ 6 := by
      calc
        _ ≤ (T : ℝ) ^ (n ^ 5) * (T : ℝ) ^ (n ^ 5) *
            (T : ℝ) ^ (n ^ 5) * (T : ℝ) ^ (n ^ 5) *
            (T : ℝ) ^ (n ^ 5) * (T : ℝ) ^ (n ^ 5) := by gcongr
        _ = ((T : ℝ) ^ (n ^ 5)) ^ 6 := by ring
    _ = (T : ℝ) ^ (6 * n ^ 5) := by
      rw [← pow_mul]
      congr 1
      ring

private theorem algebraic_real_det_loss_eq (n T degree : ℕ) :
    ((n ^ 6).factorial • (((T : ℝ) ^ (6 * n ^ 5)) ^ (n ^ 6)) : ℝ) ^
        (degree - 1) =
      ((((n ^ 6).factorial * T ^ (6 * n ^ 11)) ^ (degree - 1) : ℕ) : ℝ) := by
  simp only [nsmul_eq_mul]
  push_cast
  rw [← pow_mul]
  congr 2
  · congr 1
    ring

set_option maxHeartbeats 3000000 in
private theorem not_irrational_of_two_three_a_rpow_scaledAlgebraicInteger_of_monomial_injective
    {K : Type*} [Field K] [NumberField K]
    {a : ℕ} (ha : 1 < a)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2.1 * a ^ u.2.2))
    {x : ℝ}
    (hTwo : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (hThree : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (scale : ℕ) (hscale : 0 < scale)
    (alpha : NumberField.RingOfIntegers K) (sigma : K →+* ℂ)
    (haPow : sigma (alpha : K) =
      (scale : ℂ) * (((a : ℝ) ^ x : ℝ) : ℂ)) :
    ¬ Irrational x := by
  classical
  intro hxirr
  obtain ⟨zTwo, hzTwo⟩ := hTwo
  obtain ⟨zThree, hzThree⟩ := hThree
  have hx0 : 0 ≤ x := IntegerExponent.nonneg_of_two_rpow_integer ⟨zTwo, hzTwo⟩
  let kernelScale : ℝ := (Real.log 2 + Real.log 3 + Real.log a) * (1 + x)
  obtain ⟨D, hD⟩ := exists_nat_ge kernelScale

  let conjugateScale : ℝ :=
    2 + 3 + (a : ℝ) + |(zTwo : ℝ)| + |(zThree : ℝ)| +
      (scale : ℝ) +
      NumberField.house (alpha : K)
  obtain ⟨T, hT⟩ := exists_nat_ge conjugateScale
  have hzTwoNonneg : 0 ≤ |(zTwo : ℝ)| := abs_nonneg _
  have hzThreeNonneg : 0 ≤ |(zThree : ℝ)| := abs_nonneg _
  have hscaleNonneg : 0 ≤ (scale : ℝ) := Nat.cast_nonneg _
  have hhouseNonneg : 0 ≤ NumberField.house (alpha : K) :=
    NumberField.house_nonneg _
  have haNonneg : 0 ≤ (a : ℝ) := Nat.cast_nonneg _
  have hTTwo : (2 : ℝ) ≤ T := by
    dsimp only [conjugateScale] at hT
    nlinarith
  have hTThree : (3 : ℝ) ≤ T := by
    dsimp only [conjugateScale] at hT
    nlinarith
  have hTa : (a : ℝ) ≤ T := by
    dsimp only [conjugateScale] at hT
    nlinarith
  have hTzTwo : |(zTwo : ℝ)| ≤ T := by
    dsimp only [conjugateScale] at hT
    nlinarith
  have hTzThree : |(zThree : ℝ)| ≤ T := by
    dsimp only [conjugateScale] at hT
    nlinarith
  have hTscale : (scale : ℝ) ≤ T := by
    dsimp only [conjugateScale] at hT
    nlinarith
  have hTalpha : NumberField.house (alpha : K) ≤ T := by
    dsimp only [conjugateScale] at hT
    nlinarith
  have hTOne : (1 : ℝ) ≤ T := le_trans (by norm_num) hTTwo
  have hTNat : 2 ≤ T := by exact_mod_cast hTTwo

  let degree : ℕ := Module.finrank ℚ K
  let b : ℕ := scale * (2 * T ^ 6) ^ (degree - 1)
  let N : ℕ := 192 * D + 2 * b + 3
  let n : ℕ := 2 * N
  let m : ℕ := n ^ 6
  let r : ℕ := 32 * N ^ 6
  let C : ℕ := D * n ^ 5
  let s : ℕ := n ^ 11
  let E : ℝ := (T : ℝ) ^ (6 * n ^ 5)

  have hDN : 192 * D ≤ N := by
    dsimp only [N]
    omega
  have hNpos : 0 < N := by
    dsimp only [N]
    omega
  have hnTwo : 2 ≤ n := by
    dsimp only [n]
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

  have hrowcard : Fintype.card (AlgebraicRowBox n) = m := by
    rw [card_algebraicRowBox]
  have hcolcard : Fintype.card (AlgebraicColBox n) = m := by
    rw [card_algebraicColBox]
  let erow : Fin m ≃ AlgebraicRowBox n := (Fintype.equivFinOfCardEq hrowcard).symm
  let ecol : Fin m ≃ AlgebraicColBox n := (Fintype.equivFinOfCardEq hcolcard).symm
  let row : Fin m → ℝ := fun i ↦ algebraicRowArg a (erow i)
  let col : Fin m → ℝ := fun j ↦ algebraicColArg x (ecol j)
  let A : Matrix (Fin m) (Fin m) ℝ := fun i j ↦ Real.exp (row i * col j)
  let AO : Matrix (Fin m) (Fin m) (NumberField.RingOfIntegers K) :=
    fun i j ↦ scaledAlgebraicEntry alpha scale (n ^ 5) zTwo zThree a
      (erow i) (ecol j)
  let Q : ℕ := scale ^ (n ^ 5)

  have hrow : Function.Injective row :=
    (algebraicRowArg_injective (by omega) hmono n).comp erow.injective
  have hcol : Function.Injective col :=
    (algebraicColArg_injective hxirr n).comp ecol.injective
  have hAne : A.det ≠ 0 := by
    exact IntegerExponent.det_exp_mul_ne_zero_of_injective row col hrow hcol
  have hentryMap : ∀ i j,
      sigma ((AO i j : NumberField.RingOfIntegers K) : K) =
        (Q : ℂ) * (A i j : ℂ) := by
    intro i j
    simpa only [AO, Q, A, row, col, Nat.cast_pow] using
      (map_scaledAlgebraicEntry_eq_smul_exp alpha sigma (by omega) hzTwo
        hzThree haPow (erow i) (ecol j)
        (algebraic_coordinate_mul_le (erow i).2.2 (ecol j).2))
  let f : NumberField.RingOfIntegers K →+* ℂ :=
    sigma.comp (algebraMap (NumberField.RingOfIntegers K) K)
  have hmatrixMap : f.mapMatrix AO = (Q : ℂ) • A.map Complex.ofReal := by
    ext i j
    change sigma ((AO i j : NumberField.RingOfIntegers K) : K) =
      (Q : ℂ) * (A i j : ℂ)
    simpa only [Matrix.smul_apply, smul_eq_mul] using hentryMap i j
  have hdetOfReal : Matrix.det (A.map Complex.ofReal) = (A.det : ℂ) := by
    have hmatrix : Complex.ofRealHom.mapMatrix A = A.map Complex.ofReal := by
      ext i j
      rfl
    calc
      Matrix.det (A.map Complex.ofReal) =
          Matrix.det (Complex.ofRealHom.mapMatrix A) := by rw [hmatrix]
      _ = Complex.ofRealHom A.det := (Complex.ofRealHom.map_det A).symm
      _ = (A.det : ℂ) := rfl
  have hdetMap : f AO.det = (Q : ℂ) ^ m * (A.det : ℂ) := by
    calc
      f AO.det = Matrix.det (f.mapMatrix AO) := f.map_det AO
      _ = Matrix.det ((Q : ℂ) • A.map Complex.ofReal) := by rw [hmatrixMap]
      _ = (Q : ℂ) ^ m * Matrix.det (A.map Complex.ofReal) := by
        rw [Matrix.det_smul, Fintype.card_fin]
      _ = (Q : ℂ) ^ m * (A.det : ℂ) := by rw [hdetOfReal]
  have hAOdet : AO.det ≠ 0 := by
    intro hzero
    have hQne : (Q : ℂ) ≠ 0 := by
      exact_mod_cast (pow_ne_zero (n ^ 5) (Nat.ne_of_gt hscale))
    have hAdetC : (A.det : ℂ) ≠ 0 := by exact_mod_cast hAne
    have hprod : (Q : ℂ) ^ m * (A.det : ℂ) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hQne) hAdetC
    apply hprod
    rw [← hdetMap, hzero, map_zero]

  have hentryBound : ∀ (tau : K →+* ℂ) i j,
      ‖tau ((AO i j : NumberField.RingOfIntegers K) : K)‖ ≤ E := by
    intro tau i j
    simpa only [AO, E] using
      (norm_map_scaledAlgebraicEntry_le alpha scale zTwo zThree hTOne hTTwo
        hTThree hTa hTzTwo hTzThree hTscale hTalpha tau (erow i) (ecol j))
  have hlowerRaw :=
    IntegerExponent.one_div_entry_bound_le_scaled_norm_det AO hAOdet
      (A.map Complex.ofReal) sigma Q hentryMap hentryBound
  have hlower :
      1 / ((m.factorial • E ^ m : ℝ) ^ (degree - 1)) ≤
        (scale : ℝ) ^ s * |A.det| := by
    have hpowExp : n ^ 5 * m = s := by
      dsimp only [m, s]
      ring
    have hQpow : (Q : ℝ) ^ m = (scale : ℝ) ^ s := by
      calc
        (Q : ℝ) ^ m = ((scale : ℝ) ^ (n ^ 5)) ^ m := by
          simp only [Q, Nat.cast_pow]
        _ = (scale : ℝ) ^ (n ^ 5 * m) := by rw [pow_mul]
        _ = (scale : ℝ) ^ s := by rw [hpowExp]
    have hselectedNorm : ‖Matrix.det (A.map Complex.ofReal)‖ = |A.det| := by
      rw [hdetOfReal, Complex.norm_real, Real.norm_eq_abs]
    simpa only [Fintype.card_fin, degree, hQpow, hselectedNorm] using hlowerRaw

  have hlossNat :
      scale ^ s *
          ((n ^ 6).factorial * T ^ (6 * n ^ 11)) ^ (degree - 1) ≤ b ^ s := by
    simpa only [b, s] using
      (IntegerExponent.combined_algebraic_loss_le_uniform_power
        n T degree scale hnTwo)
  have hdenEq :
      (m.factorial • E ^ m : ℝ) ^ (degree - 1) =
        (((n ^ 6).factorial * T ^ (6 * n ^ 11)) ^ (degree - 1) : ℕ) := by
    simpa only [m, E] using algebraic_real_det_loss_eq n T degree
  have hdenLe :
      (scale : ℝ) ^ s *
          (m.factorial • E ^ m : ℝ) ^ (degree - 1) ≤ (b : ℝ) ^ s := by
    rw [hdenEq]
    exact_mod_cast hlossNat
  have hdenPos : 0 < (m.factorial • E ^ m : ℝ) ^ (degree - 1) := by
    have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hTOne
    dsimp only [E]
    positivity
  have hkernel : ∀ i j, |row i * col j| ≤ (C : ℝ) := by
    intro i j
    change |algebraicRowArg a (erow i) * algebraicColArg x (ecol j)| ≤ (C : ℝ)
    simpa only [C] using
      (algebraic_abs_rowArg_mul_colArg_le ha hx0
        (by simpa only [kernelScale] using hD) (erow i) (ecol j))
  have hupper : |A.det| ≤
      (2 : ℝ) ^ m * (m.factorial : ℝ) * Real.exp (C : ℝ) ^ r *
        (Real.exp (C : ℝ) * (C : ℝ) ^ r / (r.factorial : ℝ)) ^ (m - r) := by
    change |Matrix.det (fun i j ↦ Real.exp (row i * col j))| ≤ _
    exact IntegerExponent.abs_det_exp_mul_le hrm row col (C : ℝ)
      (Nat.cast_nonneg _) hkernel hsmall
  have hone_le : 1 ≤ (b : ℝ) ^ s * |A.det| := by
    have hone : 1 ≤
        (m.factorial • E ^ m : ℝ) ^ (degree - 1) *
          ((scale : ℝ) ^ s * |A.det|) := by
      have h := (div_le_iff₀ hdenPos).mp hlower
      simpa [mul_comm] using h
    calc
      1 ≤ (m.factorial • E ^ m : ℝ) ^ (degree - 1) *
          ((scale : ℝ) ^ s * |A.det|) := hone
      _ = ((scale : ℝ) ^ s *
          (m.factorial • E ^ m : ℝ) ^ (degree - 1)) * |A.det| := by ring
      _ ≤ (b : ℝ) ^ s * |A.det| :=
        mul_le_mul_of_nonneg_right hdenLe (abs_nonneg _)
  have hscaledUpper : (b : ℝ) ^ s * |A.det| ≤
      (b : ℝ) ^ s *
        ((2 : ℝ) ^ m * (m.factorial : ℝ) * Real.exp (C : ℝ) ^ r *
          (Real.exp (C : ℝ) * ((C : ℝ) ^ r / (r.factorial : ℝ))) ^ (m - r)) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
    simpa only [mul_div_assoc] using hupper
  have : (1 : ℝ) < 1 :=
    lt_of_le_of_lt (hone_le.trans hscaledUpper) hnumeric
  exact lt_irrefl 1 this

/-- If `2 ^ x` and `3 ^ x` are integers and `a ^ x` is represented by an algebraic
integer in a number field, injectivity of the `2,3,a` monomials forces `x` rational. -/
theorem rational_of_two_three_a_rpow_algebraicInteger_of_monomial_injective
    {K : Type*} [Field K] [NumberField K]
    {a : ℕ} (ha : 1 < a)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2.1 * a ^ u.2.2))
    {x : ℝ}
    (hTwo : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (hThree : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (alpha : NumberField.RingOfIntegers K) (sigma : K →+* ℂ)
    (haPow : sigma (alpha : K) = (((a : ℝ) ^ x : ℝ) : ℂ)) :
    x ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  exact not_not.mp
    (not_irrational_of_two_three_a_rpow_scaledAlgebraicInteger_of_monomial_injective
      ha hmono hTwo hThree 1 (by omega) alpha sigma (by simpa using haPow))

/-- The rational conclusion upgrades to integrality because `2 ^ x` is integral. -/
theorem integer_of_two_three_a_rpow_algebraicInteger_of_monomial_injective
    {K : Type*} [Field K] [NumberField K]
    {a : ℕ} (ha : 1 < a)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2.1 * a ^ u.2.2))
    {x : ℝ}
    (hTwo : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (hThree : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (alpha : NumberField.RingOfIntegers K) (sigma : K →+* ℂ)
    (haPow : sigma (alpha : K) = (((a : ℝ) ^ x : ℝ) : ℂ)) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  apply IntegerExponent.integer_of_rational_of_two_rpow_integer
  · exact rational_of_two_three_a_rpow_algebraicInteger_of_monomial_injective
      ha hmono hTwo hThree alpha sigma haPow
  · exact hTwo

/-- If the third natural-base output is algebraic over `ℚ`, injectivity of the
`2,3,a` monomials forces the exponent to be rational.  A natural denominator is
absorbed uniformly into the interpolation determinant. -/
theorem rational_of_two_three_a_rpow_isAlgebraic_of_monomial_injective
    {a : ℕ} (ha : 1 < a)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2.1 * a ^ u.2.2))
    {x : ℝ}
    (hTwo : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (hThree : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (haAlg : IsAlgebraic ℚ ((a : ℝ) ^ x)) :
    x ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  let B := IntegerExponent.AlgebraicOutputBridge.ofRealIsAlgebraic haAlg
  letI : Field B.K := B.fieldK
  letI : NumberField B.K := B.numberFieldK
  have hmap : B.embedding (B.integer : B.K) =
      (B.denominator : ℂ) * (((a : ℝ) ^ x : ℝ) : ℂ) := by
    rw [← B.denominator_smul_eq_map_integer]
    simp only [nsmul_eq_mul]
  exact not_not.mp
    (not_irrational_of_two_three_a_rpow_scaledAlgebraicInteger_of_monomial_injective
      ha hmono hTwo hThree B.denominator
        (Nat.pos_of_ne_zero B.denominator_ne_zero) B.integer B.embedding hmap)

/-- The algebraic-output conclusion upgrades from rationality to integrality because
the output at base `2` is an integer. -/
theorem integer_of_two_three_a_rpow_isAlgebraic_of_monomial_injective
    {a : ℕ} (ha : 1 < a)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2.1 * a ^ u.2.2))
    {x : ℝ}
    (hTwo : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (hThree : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (haAlg : IsAlgebraic ℚ ((a : ℝ) ^ x)) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  apply IntegerExponent.integer_of_rational_of_two_rpow_integer
  · exact rational_of_two_three_a_rpow_isAlgebraic_of_monomial_injective
      ha hmono hTwo hThree haAlg
  · exact hTwo

end


end LeanProofs.TwoBaseIntegerExponent
