import DiophantineConsistency.CurrentCarryConstruction2011

namespace DiophantineConsistency.CurrentCarryConstruction2011Checks

open NativeCyclicConvolution CurrentKernel2011 CurrentCarryConstruction2011

set_option Elab.async false

-- The actual fixed kernel normalizes any Boolean word, including a
-- displacement that is not a whole 47-bit field.
example {n : ℕ} [NeZero n] (c : ZMod n → ℕ) (hc : ∀ i, c i ≤ 1) :
    ∃ k digits : ZMod n → ℕ, Facts c 46 k digits := exists_normalization c hc 46

-- Single-field cyclic predecessor and arbitrary large phase remain valid.
example (c : ZMod 1 → ℕ) (hc : ∀ i, c i ≤ 1) (W : ℕ) :
    ∃ k digits : ZMod 1 → ℕ, Facts c W k digits := exists_normalization c hc W

-- The zero word is permitted: normalization does not promise positivity.
example (W : ℕ) : ∃ k digits : ZMod 1 → ℕ, Facts (fun _ => 0) W k digits :=
  exists_normalization _ (fun _ => by omega) W
example : ¬ 0 < word radix (fun _ : ZMod 1 => 0) := by simp [word]

-- One slack digit excludes the exceptional maximum word; all other digits
-- may reach radix-1. Positivity needs its own positive digit.
example {n : ℕ} [NeZero n] {c k digits : ZMod n → ℕ} {W : ℕ}
    (h : Facts c W k digits) (i j : ZMod n)
    (hi : digits i < radix-1) (hj : 0 < digits j) :
    0 < word radix digits ∧ word radix digits < radix^n-1 :=
  ⟨word_pos_of_digit digits j hj,h.word_lt i hi⟩

-- Independent dummy/marker controls suffice to construct the full
-- assembled normalization, with no source zero or mask hypothesis.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942)
    (dummy marker : ZMod N → ℕ) (hd : ∀ j, dummy j ≤ 1)
    (hm : ∀ j, marker j ≤ 1) (W : ℕ) :
    ∃ k digits : ZMod (N*2011) → ℕ,
      Facts (CurrentWordConstruction2011.word a dummy marker) W k digits :=
  exists_assembled_normalization a dummy marker hd hm W

-- Start at the origin makes C positive even before the carry/mask steps.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942)
    (dummy marker : ZMod N → ℕ) (s : ℤ) (h : WangTiles942Periodic.MarkedWord N s a) :
    0 < word radix (CurrentWordConstruction2011.word a dummy marker) :=
  assembled_source_pos a dummy marker s h

#print axioms CurrentCarryConstruction2011.exists_normalization
#print axioms word_pos_of_digit
#print axioms Facts.word_lt
#print axioms exists_assembled_normalization
#print axioms assembled_source_pos

end DiophantineConsistency.CurrentCarryConstruction2011Checks
