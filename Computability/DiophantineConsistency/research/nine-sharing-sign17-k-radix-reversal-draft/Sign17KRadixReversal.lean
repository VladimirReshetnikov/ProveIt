import DiophantineConsistency.Sign17KOfDigitsSum

/-! SOURCE ONLY. Generic reversal and single-digit increment. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KRadixReversal
open scoped BigOperators

theorem rev_bijective (n : ℕ) : Function.Bijective (Fin.rev : Fin n → Fin n) := by
  constructor
  · intro i j h
    simpa only [Fin.rev_rev] using congrArg Fin.rev h
  · intro i
    exact ⟨i.rev, Fin.rev_rev i⟩

theorem ofDigits_reversed (r n : ℕ) (v : Fin n → ℕ) :
    Nat.ofDigits r (List.ofFn (fun i => v i.rev)) =
      ∑ i : Fin n, v i * r ^ (n - (i.val + 1)) := by
  rw [Sign17KOfDigitsSum.ofDigits_ofFn_sum]
  calc
    (∑ i : Fin n, v i.rev * r ^ i.val) =
        ∑ i : Fin n, v i * r ^ i.rev.val := by
      simpa only [Fin.rev_rev] using
        (rev_bijective n).sum_comp (fun i : Fin n => v i * r ^ i.rev.val)
    _ = ∑ i : Fin n, v i * r ^ (n - (i.val + 1)) := by
      simp only [Fin.val_rev]

theorem ofDigits_increment (r n : ℕ) (v : Fin n → ℕ) (k : Fin n) :
    Nat.ofDigits r (List.ofFn (fun i => v i + if i = k then 1 else 0)) =
      Nat.ofDigits r (List.ofFn v) + r ^ k.val := by
  classical
  rw [Sign17KOfDigitsSum.ofDigits_ofFn_sum, Sign17KOfDigitsSum.ofDigits_ofFn_sum]
  simp only [Nat.add_mul, Finset.sum_add_distrib]
  congr 1
  simp

end DiophantineConsistency.Sign17KRadixReversal
#print axioms DiophantineConsistency.Sign17KRadixReversal.ofDigits_reversed
#print axioms DiophantineConsistency.Sign17KRadixReversal.ofDigits_increment
