import DiophantineConsistency.ArithmeticMaskData
import DiophantineConsistency.MFPaper1982Digits

/-! Source-only draft of the printed high-mask identity. The geometric helper
is the already authenticated `ArithmeticMaskData.G`; no native mask, Wilson,
or printed-port extension module is imported. This draft has not been checked. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
noncomputable section

namespace DiophantineConsistency.Current14HighMaskMF
open CurrentMasks2011 ArithmeticMaskData
open scoped BigOperators

/-- Integer geometric sum used by the displayed page. -/
def geomInt (r : ℤ) (n : ℕ) : ℤ := ∑ j ∈ Finset.range n, r ^ j

theorem G_cast (r n : ℕ) : (G r n : ℤ) = geomInt r n := by
  rw [← sum_range_pow]
  simp [geomInt]

theorem geomInt_succ (r : ℤ) (n : ℕ) :
    geomInt r (n + 1) = 1 + r * geomInt r n := by
  unfold geomInt
  rw [Finset.sum_range_succ']
  simp only [pow_zero, pow_succ, ← Finset.sum_mul]
  ring

/-- First normalize the finite radix digits, keeping subtraction in ℕ. -/
theorem highPort_nat_recipe : highPort =
    4 + 8 * radix * G radix 916 +
      radix ^ 960 * G radix 9 + radix ^ 987 * G radix 8 +
      radix ^ 1004 + (2 ^ 45 - 4) * radix ^ 1005 := by
  unfold highPort highDigits
  rw [Nat.ofDigits_append_replicate_zero]
  unfold highPrefix
  simp only [Nat.ofDigits_cons, Nat.ofDigits_nil, ofDigits_replicate_append,
    G_zero, G_one, List.length_append, List.length_replicate,
    mul_zero, zero_mul, add_zero, zero_add]
  norm_num only [Nat.reduceAdd]
  ring

/-- The printed high-mask term, before the separate beta shift. -/
theorem highPort_int_recipe : (highPort : ℤ) =
    8 * geomInt radix 917 - 4 +
      (2 ^ 45 - 4) * (radix : ℤ) ^ 1005 +
      (radix : ℤ) ^ 960 * geomInt radix 9 +
      (radix : ℤ) ^ 987 * geomInt radix 8 + (radix : ℤ) ^ 1004 := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) highPort_nat_recipe
  push_cast [Nat.cast_sub (by decide : 4 ≤ (2 : ℕ) ^ 45)] at h
  simp only [G_cast] at h
  rw [show 917 = 916 + 1 from rfl, geomInt_succ]
  linear_combination h

#print axioms highPort_nat_recipe
#print axioms highPort_int_recipe
end DiophantineConsistency.Current14HighMaskMF
