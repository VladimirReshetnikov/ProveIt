import DiophantineConsistency.NativeCyclicCarryWord

/-!
# Focused checks for cyclic carry words

The first example has a genuine carry through the last-to-first boundary.
The one-field example checks the degenerate cyclic rotation separately.
The last example records why a zero transport residue does not identify
the all-maximum-digit representative with zero.
-/

namespace DiophantineConsistency.NativeCyclicCarryWordAudit

open NativeCyclicConvolution NativeCyclicCarryWord

private def raw3 (i : ZMod 3) : ℕ := if i = 0 then 9 else if i = 1 then 0 else 20
private def carry3 (i : ZMod 3) : ℕ := if i = 0 then 1 else if i = 1 then 0 else 2

theorem recurrence3 : ∀ i, carry3 i = (raw3 i + carry3 (i - 1)) / 10 := by decide

theorem wrapped_word :
    word 10 raw3 = 2009 ∧
    word 10 (NativeCyclicCarry.digit 10 raw3 (fun i => i - 1) carry3) = 11 ∧
    NativeCyclicCarry.digit 10 raw3 (fun i => i - 1) carry3 0 = 1 ∧
    raw3 0 % 10 = 9 := by decide

theorem normalized3 :
    word 10 (NativeCyclicCarry.digit 10 raw3 (fun i => i - 1) carry3) = 11 := by
  exact transport_word_eq (by decide) raw3 carry3 recurrence3
    (by decide) (by decide) (by decide)

theorem existence3 :
    ∃ k digits : ZMod 3 → ℕ, (∀ i, k i ≤ 2) ∧ (∀ i, digits i < 10) ∧
      (∀ i, k i = (raw3 i + k (i - 1)) / 10) ∧
      (∀ i, raw3 i + k (i - 1) = digits i + 10 * k i) ∧ word 10 digits = 11 := by
  exact exists_normalization (by decide) raw3 (by decide)
    (by decide) (by decide) (by decide)

theorem one_field :
    word 10 (NativeCyclicCarry.digit 10 (fun _ : ZMod 1 => 25)
      (fun i => i - 1) (fun _ => 2)) = 7 := by
  exact transport_word_eq (by decide) (fun _ : ZMod 1 => 25) (fun _ => 2)
    (by decide) (by decide) (by decide) (by decide)

/-- If positivity is dropped, all-maximum digits give a second representative. -/
theorem zero_residue_boundary :
    (∀ _ : ZMod 3, 9 < (10 : ℕ)) ∧
    word 10 (fun _ : ZMod 3 => 9) = 10 ^ 3 - 1 ∧
    (word 10 (fun _ : ZMod 3 => 9) ≡ 0 [MOD 10 ^ 3 - 1]) ∧
    word 10 (fun _ : ZMod 3 => 9) ≠ 0 := by decide

#print axioms word_congruent_of_recurrence
#print axioms word_eq_of_congruent
#print axioms exists_normalization
#print axioms exists_convolution_normalization
#print axioms NativeCyclicCarryWord.transport_mask_digits
#print axioms normalized3
#print axioms one_field
#print axioms zero_residue_boundary

end DiophantineConsistency.NativeCyclicCarryWordAudit
