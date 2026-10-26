import DiophantineConsistency.CurrentSouthShift2011
import DiophantineConsistency.NativeFieldCycles2011

/-! Checks of generic Boolean prefix reconstruction, the actual physical
source positions, and composition with the generic offset20 exclusion. -/

namespace DiophantineConsistency.CurrentSouthShift2011Checks

open CurrentCellLabels2011 CurrentCellTranslation2011 CurrentSouthShift2011
open scoped BigOperators

set_option Elab.async false

example (f : ℕ → ℕ) (hf : ∀ j, f j ≤ 1) :
    binaryWord f 9 = (2 * binaryWord (fun j => f (1+j)) 9) % 512 + f 0 := by
  have h := binaryWord_prefix f 1 8 (fun j _ => hf (1+j))
  norm_num only [Nat.reduceAdd, Nat.reducePow] at h
  simpa only [binaryWord, Finset.sum_range_one, pow_zero, one_mul] using h

example (f : ℕ → ℕ) (hf : ∀ j, f j ≤ 1) :
    binaryWord f 9 = (4 * binaryWord (fun j => f (2+j)) 9) % 512 + f 0 + 2*f 1 := by
  have h := binaryWord_prefix f 2 7 (fun j _ => hf (2+j))
  have hp : binaryWord f 2 = f 0 + 2*f 1 := by
    simp [binaryWord, Finset.sum_range_succ]
  rw [hp] at h
  change binaryWord f 9 = (4 * binaryWord (fun j => f (2+j)) 9) % 512 + (f 0 + 2*f 1) at h
  omega

variable {N : ℕ} [NeZero (N * 2011)]

example (c : ZMod (N * 2011) → ℕ) (hc : ∀ k, c k ≤ 1) (b : Cell N) :
    southWord c b < 512 := southWord_lt c hc b

example (c : ZMod (N * 2011) → ℕ) (hc : ∀ k, c k ≤ 1)
    (t : ℕ) (b : Cell N) (hr : t % 2011 = 19)
    (hcopy : ∀ j : Fin 9,
      c ((b : ZMod (N * 2011)) + ((942+j.val : ℕ) : ZMod (N * 2011))) =
      c ((b : ZMod (N * 2011)) + ((960+j.val : ℕ) : ZMod (N * 2011)) -
        (t : ZMod (N * 2011)))) :
    southWord c b = (2*southWord c (theta t b)) % 512 +
      c (((theta t b : Cell N) : ZMod (N * 2011)) + 941) :=
  offset19_word c hc t b hr hcopy

/-- All nine actual copy equalities plus a physical at-most-one count
already rule out South510 at offset20. No label interpretation is used. -/
example (c : ZMod (N * 2011) → ℕ) (hc : ∀ k, c k ≤ 1)
    (t : ℕ) (hr : t % 2011 = 20)
    (hcopy : ∀ b : Cell N, ∀ j : Fin 9,
      c ((b : ZMod (N * 2011)) + ((942+j.val : ℕ) : ZMod (N * 2011))) =
      c ((b : ZMod (N * 2011)) + ((960+j.val : ℕ) : ZMod (N * 2011)) -
        (t : ZMod (N * 2011))))
    (hone : ∀ b : Cell N, (∑ j : Fin 942,
      c ((b : ZMod (N * 2011)) + (j.val : ZMod (N * 2011)))) ≤ 1) :
    ∀ b : Cell N, southWord c b ≠ 510 := by
  apply NativeFieldCycles2011.offset20_excludes_510 (theta t) (southWord c)
    (fun b => c (((theta t b : Cell N) : ZMod (N * 2011)) + 940) +
      2*c (((theta t b : Cell N) : ZMod (N * 2011)) + 941))
  · intro b
    exact offset20_error_le_two c t b (hone (theta t b))
  · intro b
    have hh := offset20_word c hc t b hr (hcopy b)
    omega

#print axioms binaryWord_append
#print axioms binaryWord_prefix
#print axioms southWord_lt
#print axioms copy_word_translation
#print axioms offset19_word
#print axioms offset20_word
#print axioms offset20_error_le_two

end DiophantineConsistency.CurrentSouthShift2011Checks
