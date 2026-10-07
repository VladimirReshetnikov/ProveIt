import GowersSzemeredi.Section05

/-! Finite numerical budgets for a quadratic recurrence argument. These
lemmas control the denominator supplied by a normalized Weyl estimate;
they do not assert the Fourier witness or the recurrence itself. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def quadraticRecurrenceSample (R : Real) : Real := 2 ^ (256 : Nat) * R ^ 16
def quadraticRecurrenceRoot (R : Real) : Real := 2 ^ (128 : Nat) * R ^ 8

theorem quadraticRecurrenceSample_eq_sq (R : Real) :
    quadraticRecurrenceSample R = quadraticRecurrenceRoot R ^ 2 := by
  unfold quadraticRecurrenceSample quadraticRecurrenceRoot
  ring

theorem quadraticRecurrenceSample_natCast (R : Nat) :
    ((2 ^ 256 * R ^ 16 : Nat) : Real) = quadraticRecurrenceSample R := by
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, quadraticRecurrenceSample]

theorem quadraticRecurrenceRoot_pos {R : Real} (hR : 0 < R) :
    0 < quadraticRecurrenceRoot R := by
  unfold quadraticRecurrenceRoot
  positivity

theorem quadraticRecurrenceSample_sqrt (R : Real) :
    Real.sqrt (quadraticRecurrenceSample R) = quadraticRecurrenceRoot R := by
  rw [quadraticRecurrenceSample_eq_sq, Real.sqrt_sq]
  unfold quadraticRecurrenceRoot
  positivity

theorem quadraticRecurrenceSample_nat_large {R : Nat} (hR : 2 ≤ R) :
    4 * R ≤ 2 ^ 256 * R ^ 16 := by
  have hp : R ≤ R ^ 16 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ R) (by omega : 1 ≤ 16)
  exact Nat.mul_le_mul (by norm_num) hp

theorem quadraticRecurrence_log_bound {R : Real} (hR : 2 ≤ R) :
    1 + Real.log (quadraticRecurrenceSample R) ≤ 145 * R := by
  have hR0 : 0 < R := by linarith
  unfold quadraticRecurrenceSample
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
  have hr := Real.log_le_sub_one_of_pos hR0
  norm_num only [Nat.cast_ofNat] at *
  linarith

theorem quadraticRecurrence_error_bound {R : Real} (hR : 2 ≤ R) :
    2 ^ (26 : Nat) * quadraticRecurrenceRoot R *
        (1 + Real.log (quadraticRecurrenceSample R)) / quadraticRecurrenceSample R ≤
      1 / (128 * R ^ 2) := by
  have hR0 : 0 < R := by linarith
  have hD : 0 < quadraticRecurrenceRoot R := by unfold quadraticRecurrenceRoot; positivity
  have hp : R ^ 3 ≤ R ^ 8 := pow_le_pow_right₀ (by linarith) (by omega)
  have hbudget : (128 * R ^ 2) * (2 ^ (26 : Nat) * (145 * R)) ≤ quadraticRecurrenceRoot R := by
    calc
      _ = (128 * 2 ^ (26 : Nat) * 145) * R ^ 3 := by ring
      _ ≤ (2 : Real) ^ (128 : Nat) * R ^ 8 :=
        mul_le_mul (by norm_num) hp (by positivity) (by positivity)
      _ = quadraticRecurrenceRoot R := rfl
  calc
    _ = 2 ^ (26 : Nat) * (1 + Real.log (quadraticRecurrenceSample R)) /
        quadraticRecurrenceRoot R := by
      rw [quadraticRecurrenceSample_eq_sq]
      field_simp
    _ ≤ 2 ^ (26 : Nat) * (145 * R) / quadraticRecurrenceRoot R := by
      gcongr
      exact quadraticRecurrence_log_bound hR
    _ ≤ 1 / (128 * R ^ 2) := by
      apply (div_le_div_iff₀ hD (by positivity)).mpr
      simpa only [one_mul, mul_comm] using hbudget

theorem quadraticRecurrence_denominator_bound {R q : Real} (hR : 2 ≤ R) (hq : 0 < q)
    (hweyl : 1 / (64 * R ^ 2) ≤
      2 ^ (25 : Nat) * quadraticRecurrenceRoot R *
        (q⁻¹ + 2 / quadraticRecurrenceSample R) *
          (1 + Real.log (quadraticRecurrenceSample R))) :
    q ≤ 2 ^ (40 : Nat) * quadraticRecurrenceRoot R * R ^ 3 := by
  have hR0 : 0 < R := by linarith
  have hD : 0 < quadraticRecurrenceRoot R := by unfold quadraticRecurrenceRoot; positivity
  have herr := quadraticRecurrence_error_bound hR
  have hsplit : 2 ^ (25 : Nat) * quadraticRecurrenceRoot R *
      (q⁻¹ + 2 / quadraticRecurrenceSample R) *
        (1 + Real.log (quadraticRecurrenceSample R)) =
      (2 ^ (25 : Nat) * quadraticRecurrenceRoot R *
        (1 + Real.log (quadraticRecurrenceSample R))) / q +
      2 ^ (26 : Nat) * quadraticRecurrenceRoot R *
        (1 + Real.log (quadraticRecurrenceSample R)) / quadraticRecurrenceSample R := by ring
  rw [hsplit] at hweyl
  have hhalf : 1 / (64 * R ^ 2) = 2 * (1 / (128 * R ^ 2)) := by ring
  rw [hhalf] at hweyl
  have hlo : 1 / (128 * R ^ 2) ≤
      (2 ^ (25 : Nat) * quadraticRecurrenceRoot R *
        (1 + Real.log (quadraticRecurrenceSample R))) / q := by linarith
  have hprod := (le_div_iff₀ hq).mp hlo
  have hq' : q ≤ (2 ^ (25 : Nat) * quadraticRecurrenceRoot R *
      (1 + Real.log (quadraticRecurrenceSample R))) * (128 * R ^ 2) := by
    apply (div_le_iff₀ (by positivity : 0 < 128 * R ^ 2)).mp
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hprod
  calc
    q ≤ _ := hq'
    _ ≤ (2 ^ (25 : Nat) * quadraticRecurrenceRoot R * (145 * R)) * (128 * R ^ 2) := by
      gcongr
      exact quadraticRecurrence_log_bound hR
    _ ≤ 2 ^ (40 : Nat) * quadraticRecurrenceRoot R * R ^ 3 := by
      have hcoef : (2 : Real) ^ (25 : Nat) * 145 * 128 ≤ 2 ^ (40 : Nat) := by norm_num
      have h := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ quadraticRecurrenceRoot R * R ^ 3 by positivity)
      nlinarith [h]

theorem quadraticRecurrence_witness_budget {R h q : Real} (hR : 2 ≤ R)
    (hhR : h ≤ 4 * R ^ 2) (hq : 0 ≤ q)
    (hqR : q ≤ 2 ^ (40 : Nat) * quadraticRecurrenceRoot R * R ^ 3) :
    h * q < quadraticRecurrenceSample R / R ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hD : 0 < quadraticRecurrenceRoot R := by unfold quadraticRecurrenceRoot; positivity
  have hsmall : (2 : Real) ^ (42 : Nat) * R ^ 7 < quadraticRecurrenceRoot R := by
    calc
      _ < (2 : Real) ^ (128 : Nat) * R ^ 7 :=
        mul_lt_mul_of_pos_right (by norm_num) (by positivity)
      _ ≤ (2 : Real) ^ (128 : Nat) * R ^ 8 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) (by omega)) (by positivity)
      _ = quadraticRecurrenceRoot R := rfl
  calc
    h * q ≤ (4 * R ^ 2) * (2 ^ (40 : Nat) * quadraticRecurrenceRoot R * R ^ 3) :=
      mul_le_mul hhR hqR hq (by positivity)
    _ = 2 ^ (42 : Nat) * quadraticRecurrenceRoot R * R ^ 5 := by ring
    _ < quadraticRecurrenceSample R / R ^ 2 := by
      apply (lt_div_iff₀ (by positivity : 0 < R ^ 2)).mpr
      rw [quadraticRecurrenceSample_eq_sq]
      have h := mul_lt_mul_of_pos_right hsmall hD
      nlinarith [h]

end LeanProofs.GowersSzemeredi
