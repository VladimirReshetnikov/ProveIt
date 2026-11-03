import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.GetD

/-! Generic bounded digit-window reconstruction, with no concrete numeral. -/
set_option autoImplicit false
set_option Elab.async false
namespace RadixWindowReconstruction

theorem getD_digitsAppend (b len n i : ℕ) :
    (Nat.digitsAppend b len n).getD i 0 = (Nat.digits b n).getD i 0 := by
  unfold Nat.digitsAppend
  by_cases hi : i < (Nat.digits b n).length
  · rw [List.getD_append _ _ _ _ hi]
  · have hle : (Nat.digits b n).length ≤ i := Nat.le_of_not_gt hi
    rw [List.getD_append_right _ _ _ _ hle, List.getD_eq_default _ _ hle]
    simp

/-- Any list of digits whose windows match a bounded number decodes to it.
    In particular, all listed digits are automatically below the radix. -/
theorem ofDigits_eq_of_windows (b : ℕ) (hb : 2 ≤ b) (n : ℕ) (xs : List ℕ)
    (hn : n < b ^ xs.length)
    (hw : ∀ i, i < xs.length → xs.getD i 0 = n / b ^ i % b) :
    Nat.ofDigits b xs = n := by
  have hlen : (Nat.digitsAppend b xs.length n).length = xs.length :=
    Nat.length_digitsAppend (by omega) xs.length hn
  have hxs : xs = Nat.digitsAppend b xs.length n := by
    apply List.ext_getElem hlen.symm
    intro i hi hj
    rw [← List.getD_eq_getElem xs 0 hi,
      ← List.getD_eq_getElem (Nat.digitsAppend b xs.length n) 0 hj]
    rw [hw i hi, getD_digitsAppend, Nat.getD_digits n i hb]
  rw [hxs, Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]

#print axioms RadixWindowReconstruction.getD_digitsAppend
#print axioms RadixWindowReconstruction.ofDigits_eq_of_windows
end RadixWindowReconstruction
