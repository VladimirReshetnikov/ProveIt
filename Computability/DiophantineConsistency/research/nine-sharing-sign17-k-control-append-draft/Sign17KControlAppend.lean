import DiophantineConsistency.Sign17KRankedRawWord

/-! SOURCE-ONLY: generic finite concatenation of shifted power sums. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KControlAppend
open scoped BigOperators

theorem append_power_sum {m n : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ)
    (r offset : ℕ) :
    (∑ i : Fin (m + n), (Fin.append a b) i * r ^ (1005 - (offset + i.val))) =
      (∑ i : Fin m, a i * r ^ (1005 - (offset + i.val))) +
      (∑ i : Fin n, b i * r ^ (1005 - ((offset + m) + i.val))) := by
  rw [Fin.sum_univ_add (a := m) (b := n)]
  simp only [Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd,
    Nat.add_assoc]

end DiophantineConsistency.Sign17KControlAppend
#print axioms DiophantineConsistency.Sign17KControlAppend.append_power_sum
