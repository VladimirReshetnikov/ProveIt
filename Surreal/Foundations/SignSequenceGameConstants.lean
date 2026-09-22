import Surreal.Foundations.SignSequenceGames
import Surreal.Foundations.SignSequenceIntegers

/-!
# Zero and one in the sign/game bridge

The canonical games of the empty and one-plus sign sequences are literally
the upstream games zero and one. Thus the order embedding preserves the
already fixed additive zero and unit before any field is transported.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

@[simp] theorem toIGame_zero : toIGame (0 : SignSequence.{u}) = 0 := by
  apply IGame.ext
  intro p
  cases p <;> simp only [leftMoves_toIGame, rightMoves_toIGame, IGame.moves_zero]
  all_goals
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro _ ⟨i, rfl⟩
    have hi := i.val.property
    simp at hi

@[simp] theorem toSurreal_zero : toSurreal (0 : SignSequence.{u}) = 0 := by
  simp [toSurreal]

@[simp] theorem toIGame_one : toIGame (1 : SignSequence.{u}) = 1 := by
  apply IGame.ext
  intro p
  cases p with
  | left =>
    rw [leftMoves_toIGame, IGame.leftMoves_one]
    apply Set.Subset.antisymm
    · rintro _ ⟨i, rfl⟩
      have hi : i.val.val = 0 := Order.lt_one_iff.mp i.val.property
      simp only [one_eq_ofOrdinal, leftOption_ofOrdinal, hi, ofOrdinal_zero,
        toIGame_zero, Set.mem_singleton_iff]
    · intro y hy
      subst y
      refine ⟨⟨⟨0, by simp [one_eq_ofOrdinal]⟩, ?_⟩, ?_⟩
      · simp [one_eq_ofOrdinal, signAt_ofOrdinal]
      · simp [one_eq_ofOrdinal, leftOption_ofOrdinal]
  | right =>
    rw [rightMoves_toIGame, IGame.rightMoves_one]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro _ ⟨i, rfl⟩
    exact rightIndex_ofOrdinal_false 1 i

@[simp] theorem toSurreal_one : toSurreal (1 : SignSequence.{u}) = 1 := by
  simp [toSurreal]

end

end Surreal.Foundations.SignSequence
