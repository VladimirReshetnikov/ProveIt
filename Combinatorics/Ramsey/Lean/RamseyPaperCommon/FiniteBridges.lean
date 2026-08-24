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

/-- The two catalogues detect exactly the same AP subsequences in a finite
permutation. -/
theorem hasAPSubsequence_iff {n k : Nat} (sigma : Equiv.Perm (Fin n)) :
    LeanProofs.DavisEntringerGrahamSimmons1977.HasMonotoneAP
        (LeanProofs.DavisEntringerGrahamSimmons1977.finitePermutationSequence sigma) k <->
      LeanProofs.LeSaulnierVijay2011.HasAPSubsequence k
        (LeanProofs.LeSaulnierVijay2011.finitePermutationValue sigma) := by
  simp only [LeanProofs.DavisEntringerGrahamSimmons1977.HasMonotoneAP,
    LeanProofs.LeSaulnierVijay2011.HasAPSubsequence]
  constructor
  · rintro ⟨indices, hindices, hprogression⟩
    exact ⟨indices, hindices,
      (isArithmeticProgression_iff
        (fun i => LeanProofs.LeSaulnierVijay2011.finitePermutationValue sigma
          (indices i))).mp hprogression⟩
  · rintro ⟨indices, hindices, hprogression⟩
    exact ⟨indices, hindices,
      (isArithmeticProgression_iff
        (fun i => LeanProofs.LeSaulnierVijay2011.finitePermutationValue sigma
          (indices i))).mpr hprogression⟩

/-- Finite `k`-avoidance is independent of the paper-local encoding. -/
theorem finiteAPFree_iff {n k : Nat} (sigma : Equiv.Perm (Fin n)) :
    LeanProofs.DavisEntringerGrahamSimmons1977.FiniteAPFree sigma k <->
      LeanProofs.LeSaulnierVijay2011.IsFiniteKAvoiding k sigma := by
  simp only [LeanProofs.DavisEntringerGrahamSimmons1977.FiniteAPFree,
    LeanProofs.LeSaulnierVijay2011.IsFiniteKAvoiding, hasAPSubsequence_iff]

/-- The subtypes of 3-avoiding permutations in the two catalogues are
canonically equivalent. -/
noncomputable def progressionFreeEquiv (n : Nat) :
    {sigma : Equiv.Perm (Fin n) //
      LeanProofs.DavisEntringerGrahamSimmons1977.FiniteAPFree sigma 3} ≃
      {sigma : Equiv.Perm (Fin n) //
        LeanProofs.LeSaulnierVijay2011.IsFiniteKAvoiding 3 sigma} where
  toFun sigma :=
    ⟨sigma.1, (finiteAPFree_iff (n := n) (k := 3) sigma.1).mp sigma.2⟩
  invFun sigma :=
    ⟨sigma.1, (finiteAPFree_iff (n := n) (k := 3) sigma.1).mpr sigma.2⟩
  left_inv sigma := by cases sigma; rfl
  right_inv sigma := by cases sigma; rfl

/-- The counting functions `M` in the 1977 and 2011 catalogues coincide. -/
theorem davis_M_eq_lesaulnier_M (n : Nat) :
    LeanProofs.DavisEntringerGrahamSimmons1977.M n =
      LeanProofs.LeSaulnierVijay2011.M n := by
  classical
  unfold LeanProofs.DavisEntringerGrahamSimmons1977.M
    LeanProofs.LeSaulnierVijay2011.M
  exact Fintype.card_congr (progressionFreeEquiv n)

end LeanProofs.RamseyPaperCommon
