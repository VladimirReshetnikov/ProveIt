import DiophantineConsistency.CurrentSouthShift2011
import DiophantineConsistency.CurrentTileColors2011
import DiophantineConsistency.CurrentOccupation2011
import DiophantineConsistency.CurrentCellCycle2011

/-!
# Review-only simplification candidates, pinned to b310142330df89e48413c8fce62e7de223e1c7d5

UNCOMPILED: no Lean runtime was available. This file is a proposal, not a
verified patch. It imports the original modules and places alternative
proofs under fresh names; the repository snapshot is not changed.

C1 uses an API already called in NativeSelectorClause54.selectors_one.
C2 needs only the existing binaryWord_prefix; the two private helpers below
repeat helpers already in CurrentSouthShift2011, because private names are
not a public import interface. They add no helpers to the intended patch.
C3 moves the existing binaryWord_congr to CurrentCellLabels2011; this
standalone candidate instead refers to its current namespace.
C4 reorders propagate_from before propagate in the intended patch.
-/

namespace DiophantineConsistency.Round2Current

open CurrentCellLabels2011 CurrentSouthShift2011 CurrentCellTranslation2011
  CurrentAdjacency2011 CurrentOccupation2011 CurrentCellCycle2011
open scoped BigOperators

theorem sum_le_one_cases_candidate {ι : Type*} [Fintype ι] (f : ι → ℕ)
    (hf : (∑ i, f i) ≤ 1) : (∀ i, f i = 0) ∨ ∃ i, Selected f i := by
  classical
  by_cases hz : ∀ i, f i = 0
  · exact Or.inl hz
  · push_neg at hz
    obtain ⟨i, hi⟩ := hz
    have hs := Finset.sum_le_one_iff.mp hf
    refine Or.inr ⟨i, (hs i i (Finset.mem_univ i) (Finset.mem_univ i) hi hi).2, ?_⟩
    intro j hji
    by_contra hj
    exact hji (hs j i (Finset.mem_univ j) (Finset.mem_univ i) hj hi).1

private theorem binaryWord_one (f : ℕ → ℕ) : binaryWord f 1 = f 0 := by
  simp [binaryWord]

private theorem binaryWord_two (f : ℕ → ℕ) : binaryWord f 2 = f 0 + 2 * f 1 := by
  simp [binaryWord, Finset.sum_range_succ]

variable {N : ℕ} [NeZero (N * 2011)]

theorem offset19_word_candidate (c : ZMod (N * 2011) → ℕ) (hc : ∀ k, c k ≤ 1)
    (t : ℕ) (b : Cell N) (hr : t % 2011 = 19)
    (hcopy : ∀ j : Fin 9,
      c ((b : ZMod (N * 2011)) + ((942+j.val : ℕ) : ZMod (N * 2011))) =
      c ((b : ZMod (N * 2011)) + ((960+j.val : ℕ) : ZMod (N * 2011)) -
        (t : ZMod (N * 2011)))) :
    southWord c b = (2*southWord c (theta t b)) % 512 +
      c (((theta t b : Cell N) : ZMod (N * 2011)) + 941) := by
  rw [copy_word_translation c t 941 b (by omega) hcopy]
  simpa only [southWord, binaryWord_one, ← Nat.add_assoc,
    Nat.reduceAdd, Nat.reducePow, Nat.add_zero, Nat.cast_ofNat] using
    (binaryWord_prefix
      (fun j => c (((theta t b : Cell N) : ZMod (N * 2011)) +
        ((941 + j : ℕ) : ZMod (N * 2011)))) 1 8 (fun j _ => hc _))

theorem offset20_word_candidate (c : ZMod (N * 2011) → ℕ) (hc : ∀ k, c k ≤ 1)
    (t : ℕ) (b : Cell N) (hr : t % 2011 = 20)
    (hcopy : ∀ j : Fin 9,
      c ((b : ZMod (N * 2011)) + ((942+j.val : ℕ) : ZMod (N * 2011))) =
      c ((b : ZMod (N * 2011)) + ((960+j.val : ℕ) : ZMod (N * 2011)) -
        (t : ZMod (N * 2011)))) :
    southWord c b = (4*southWord c (theta t b)) % 512 +
      c (((theta t b : Cell N) : ZMod (N * 2011)) + 940) +
      2*c (((theta t b : Cell N) : ZMod (N * 2011)) + 941) := by
  rw [copy_word_translation c t 940 b (by omega) hcopy]
  simpa only [southWord, binaryWord_two, ← Nat.add_assoc,
    Nat.reduceAdd, Nat.reducePow, Nat.add_zero, Nat.cast_ofNat] using
    (binaryWord_prefix
      (fun j => c (((theta t b : Cell N) : ZMod (N * 2011)) +
        ((940 + j : ℕ) : ZMod (N * 2011)))) 2 7 (fun j _ => hc _))

theorem copy_word_translation_candidate (c : ZMod (N * 2011) → ℕ) (t a : ℕ) (b : Cell N)
    (ha : t % 2011 + a = 960)
    (hcopy : ∀ j : Fin 9,
      c ((b : ZMod (N * 2011)) + ((942+j.val : ℕ) : ZMod (N * 2011))) =
      c ((b : ZMod (N * 2011)) + ((960+j.val : ℕ) : ZMod (N * 2011)) -
        (t : ZMod (N * 2011)))) :
    southWord c b = binaryWord
      (fun j => c (((theta t b : Cell N) : ZMod (N * 2011)) +
        ((a+j : ℕ) : ZMod (N * 2011)))) 9 := by
  unfold southWord
  apply CurrentTileColors2011.binaryWord_congr
  intro j hj
  have hs := source_eq_of_remainder_le b t (960+j) (by omega)
  rw [show 960+j-t%2011 = a+j by omega] at hs
  exact (hcopy ⟨j, hj⟩).trans (congrArg c hs)

omit [NeZero (N * 2011)] in
theorem horizontal_words_candidate (c : ZMod (N * 2011) → ℕ) (b : ZMod (N * 2011))
    (hbits : ∀ j : Fin 8,
      c (b + ((969+j.val : ℕ) : ZMod (N * 2011))) =
      c (previousCell b + ((978+j.val : ℕ) : ZMod (N * 2011)))) :
    eastWord c b = westWord c (previousCell b) := by
  exact CurrentTileColors2011.binaryWord_congr _ _ 8
    (fun j hj => hbits ⟨j, hj⟩)

theorem propagate_candidate (P : Cell N → Prop) (hzero : P 0)
    (hnext : ∀ b, P b → P (next b)) : ∀ b, P b := by
  exact propagate_from P 0 hzero hnext

end DiophantineConsistency.Round2Current

-- Candidate axiom audits: execute with the pinned Lean toolchain.
#print axioms DiophantineConsistency.Round2Current.sum_le_one_cases_candidate
#print axioms DiophantineConsistency.Round2Current.offset19_word_candidate
#print axioms DiophantineConsistency.Round2Current.offset20_word_candidate
#print axioms DiophantineConsistency.Round2Current.copy_word_translation_candidate
#print axioms DiophantineConsistency.Round2Current.horizontal_words_candidate
#print axioms DiophantineConsistency.Round2Current.propagate_candidate
