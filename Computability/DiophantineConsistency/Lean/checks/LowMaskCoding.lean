import DiophantineConsistency.LowMaskCoding
import DiophantineConsistency.SelectiveCertificate52

open DiophantineConsistency LowMaskCoding
open scoped BigOperators

namespace LowMask52Check

set_option maxRecDepth 16000

/-- The actual 31 input positions; the dummy coordinate is not a code digit. -/
def inputWeights (i : Fin 31) : ℕ := SelectiveCertificate52.weights i.succ

theorem weights_injective : Function.Injective inputWeights := by decide

theorem weights_bound : ∀ i, inputWeights i < 175 := by
  intro i
  exact lt_of_le_of_lt (SelectiveCertificate52.maximum_weight i.succ) (by decide)

theorem actual_input_at_zero : inputWeights 6 = 0 := rfl

theorem dummy_excluded : ∀ i, inputWeights i ≠ 81 := by decide

/-- The exact 52 low-digit mask, with its actual variable positions. -/
def literalMask (B b : ℕ) : ℕ := B ^ 175 - 1 - (b-1) * ∑ i, B ^ inputWeights i

theorem literalMask_eq (B b : ℕ) :
    literalMask B b = indexedMask B b 175 inputWeights :=
  (indexedMask_eq B b 175 inputWeights weights_injective).symm

theorem actual_low_mask_iff {B b k v g : ℕ} (hb : b = 2 ^ k) (hB : B = 2 ^ v)
    (hbB : b < B) :
    (g < B ^ 175 ∧ g &&& literalMask B b = 0) ↔
      ∃ x : Fin 31 → ℕ, (∀ i, x i < b) ∧ g = ∑ i, x i * B ^ inputWeights i := by
  have hb1 : 1 ≤ b := by rw [hb]; exact Nat.one_le_two_pow
  rw [literalMask_eq]
  exact indexed_mask_code_iff weights_injective weights_bound hb hB (by omega) hbB.le

theorem actual_dummy_digit_zero {B b k v g : ℕ} (hb : b = 2 ^ k) (hB : B = 2 ^ v)
    (hbB : b < B) (hg : g < B ^ 175) (ht : g &&& literalMask B b = 0) :
    g / B ^ 81 % B = 0 := by
  have hb1 : 1 ≤ b := by rw [hb]; exact Nat.one_le_two_pow
  rw [literalMask_eq] at ht
  exact indexed_excluded_digit_zero weights_bound hb hB (by omega) hbB.le hg ht
    (by decide) dummy_excluded

theorem actual_constant_digit_one {B b k v g : ℕ} (hb : b = 2 ^ k) (hB : B = 2 ^ v)
    (hbB : b < B) (hg : g < B ^ 175) (ht : g &&& literalMask B b = 0) :
    (B ^ 81 + g) / B ^ 81 % B = 1 := by
  have hb1 : 1 ≤ b := by rw [hb]; exact Nat.one_le_two_pow
  exact padding_digit_one (by omega) (actual_dummy_digit_zero hb hB hbB hg ht)

theorem actual_zero_weight_digit {B b : ℕ} (hB : 1 < B) (hb : 0 < b) (hbB : b ≤ B)
    (x : Fin 31 → ℕ) (hx : ∀ i, x i < b) :
    (∑ i, x i * B ^ inputWeights i) % B = x 6 :=
  indexedCode_zero_digit weights_injective weights_bound hB hb hbB hx 6 actual_input_at_zero

theorem actual_code_injective {B b : ℕ} (hB : 1 < B) (hb : 0 < b) (hbB : b ≤ B)
    (x y : Fin 31 → ℕ) (hx : ∀ i, x i < b) (hy : ∀ i, y i < b)
    (hxy : (∑ i, x i * B ^ inputWeights i) = ∑ i, y i * B ^ inputWeights i) : x = y :=
  indexedCode_injective weights_injective weights_bound hB hb hbB hx hy hxy

end LowMask52Check

#print axioms ofDigits_maskList_add
#print axioms mask_int_eq
#print axioms mask_code_iff
#print axioms indexed_mask_code_iff
#print axioms indexedCode_injective
#print axioms LowMask52Check.weights_injective
#print axioms LowMask52Check.actual_low_mask_iff
#print axioms LowMask52Check.actual_dummy_digit_zero
#print axioms LowMask52Check.actual_constant_digit_one
#print axioms LowMask52Check.actual_zero_weight_digit
#print axioms LowMask52Check.actual_code_injective
