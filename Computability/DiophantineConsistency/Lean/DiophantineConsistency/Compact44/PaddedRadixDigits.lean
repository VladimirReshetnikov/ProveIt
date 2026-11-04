import DiophantineConsistency.Compact44.SparseRadix
set_option autoImplicit false
namespace PaddedRadixDigits

def digit (L : List ℕ) (i : ℕ) : ℕ := L[i]?.getD 0

theorem ofDigits_digit (b : ℕ) (L : List ℕ) (hb : 0 < b)
    (hL : ∀ x ∈ L, x < b) (i : ℕ) :
    (Nat.ofDigits b L / b^i) % b = digit L i := by
  by_cases hi : i < L.length
  · simpa [digit, List.getElem?_eq_getElem hi] using SparseRadix.digit_ofDigits b L hb hL i hi
  · have hd : L.drop i = [] := List.drop_eq_nil_of_le (Nat.le_of_not_gt hi)
    have hq := Nat.ofDigits_div_pow_eq_ofDigits_drop i hb L hL
    rw [hd] at hq
    simp [digit, List.getElem?_eq_none (Nat.le_of_not_gt hi), hq]

#print axioms PaddedRadixDigits.ofDigits_digit
end PaddedRadixDigits
