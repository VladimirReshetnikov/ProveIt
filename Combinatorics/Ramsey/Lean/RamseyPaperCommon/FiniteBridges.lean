import DavisEntringerGrahamSimmons1977.Definitions
import LeSaulnierVijay2011.Definitions

/-!
# Bridges between the finite permutation models

The Ramsey papers use the same finite permutations and the same notion of a
monotone arithmetic-progression subsequence, but their statement catalogues
encode values in `Int` and `Nat`, respectively.  This file proves that the two
encodings agree, so counting and recurrence proofs can be shared.
-/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.RamseyPaperCommon

/-- The Davis and LeSaulnier--Vijay value functions display the same entry. -/
theorem finitePermutationValue_coe {n : Nat} (sigma : Equiv.Perm (Fin n))
    (i : Fin n) :
    LeanProofs.DavisEntringerGrahamSimmons1977.finitePermutationSequence sigma i =
      (LeanProofs.LeSaulnierVijay2011.finitePermutationValue sigma i : Int) := by
  rfl

/-- The two catalogues define the same arithmetic progressions of natural
values after coercion to the integers. -/
theorem isArithmeticProgression_iff {k : Nat} (x : Fin k -> Nat) :
    LeanProofs.DavisEntringerGrahamSimmons1977.IsArithmeticProgression
        (fun i => (x i : Int)) <->
      LeanProofs.LeSaulnierVijay2011.IsArithmeticProgression x := by
  simp only [LeanProofs.DavisEntringerGrahamSimmons1977.IsArithmeticProgression,
    LeanProofs.LeSaulnierVijay2011.IsArithmeticProgression,
    LeanProofs.LeSaulnierVijay2011.IsArithmeticProgressionWithStep, true_and]

/-- For every linearly ordered index type, casting a natural-valued sequence
to the integers does not change whether it contains a monotone arithmetic
progression subsequence.  This is the sequence-level bridge underlying all
finite-permutation specializations. -/
theorem hasMonotoneAP_natCast_iff {I : Type*} [LinearOrder I] {k : Nat}
    (sequence : I -> Nat) :
    LeanProofs.DavisEntringerGrahamSimmons1977.HasMonotoneAP
        (fun i => (sequence i : Int)) k <->
      LeanProofs.LeSaulnierVijay2011.HasAPSubsequence k
        sequence := by
  simp only [LeanProofs.DavisEntringerGrahamSimmons1977.HasMonotoneAP,
    LeanProofs.LeSaulnierVijay2011.HasAPSubsequence]
  constructor
  · rintro ⟨indices, hindices, hprogression⟩
    exact ⟨indices, hindices,
      (isArithmeticProgression_iff
        (fun i => sequence (indices i))).mp hprogression⟩
  · rintro ⟨indices, hindices, hprogression⟩
    exact ⟨indices, hindices,
      (isArithmeticProgression_iff
        (fun i => sequence (indices i))).mpr hprogression⟩

/-- The two catalogues detect exactly the same AP subsequences in a finite
permutation. -/
theorem hasAPSubsequence_iff {n k : Nat} (sigma : Equiv.Perm (Fin n)) :
    LeanProofs.DavisEntringerGrahamSimmons1977.HasMonotoneAP
        (LeanProofs.DavisEntringerGrahamSimmons1977.finitePermutationSequence sigma) k <->
      LeanProofs.LeSaulnierVijay2011.HasAPSubsequence k
        (LeanProofs.LeSaulnierVijay2011.finitePermutationValue sigma) := by
  simpa only [← finitePermutationValue_coe] using
    hasMonotoneAP_natCast_iff
      (sequence := LeanProofs.LeSaulnierVijay2011.finitePermutationValue sigma)
      (k := k)

/-- Finite `k`-avoidance is independent of the paper-local encoding. -/
theorem finiteAPFree_iff {n k : Nat} (sigma : Equiv.Perm (Fin n)) :
    LeanProofs.DavisEntringerGrahamSimmons1977.FiniteAPFree sigma k <->
      LeanProofs.LeSaulnierVijay2011.IsFiniteKAvoiding k sigma := by
  simp only [LeanProofs.DavisEntringerGrahamSimmons1977.FiniteAPFree,
    LeanProofs.LeSaulnierVijay2011.IsFiniteKAvoiding, hasAPSubsequence_iff]

/-- For every progression length, the subtypes of avoiding permutations in the
two catalogues are canonically equivalent. -/
noncomputable def progressionFreeEquivK (n k : Nat) :
    {sigma : Equiv.Perm (Fin n) //
      LeanProofs.DavisEntringerGrahamSimmons1977.FiniteAPFree sigma k} ≃
      {sigma : Equiv.Perm (Fin n) //
        LeanProofs.LeSaulnierVijay2011.IsFiniteKAvoiding k sigma} where
  toFun sigma :=
    ⟨sigma.1, (finiteAPFree_iff (n := n) (k := k) sigma.1).mp sigma.2⟩
  invFun sigma :=
    ⟨sigma.1, (finiteAPFree_iff (n := n) (k := k) sigma.1).mpr sigma.2⟩
  left_inv sigma := by cases sigma; rfl
  right_inv sigma := by cases sigma; rfl

/-- Backwards-compatible specialization of `progressionFreeEquivK` to the
3-term progressions counted in the papers. -/
noncomputable abbrev progressionFreeEquiv (n : Nat) :=
  progressionFreeEquivK n 3

/-- The two finite encodings count the same `k`-avoiding permutations for
every `n` and every progression length `k`. -/
theorem card_finiteAPFree_eq_card_isFiniteKAvoiding (n k : Nat) :
    Nat.card {sigma : Equiv.Perm (Fin n) //
      LeanProofs.DavisEntringerGrahamSimmons1977.FiniteAPFree sigma k} =
      Nat.card {sigma : Equiv.Perm (Fin n) //
        LeanProofs.LeSaulnierVijay2011.IsFiniteKAvoiding k sigma} :=
  Nat.card_congr (progressionFreeEquivK n k)

/-- The counting functions `M` in the 1977 and 2011 catalogues coincide. -/
theorem davis_M_eq_lesaulnier_M (n : Nat) :
    LeanProofs.DavisEntringerGrahamSimmons1977.M n =
      LeanProofs.LeSaulnierVijay2011.M n := by
  classical
  unfold LeanProofs.DavisEntringerGrahamSimmons1977.M
    LeanProofs.LeSaulnierVijay2011.M
  exact Fintype.card_congr (progressionFreeEquiv n)

end LeanProofs.RamseyPaperCommon
