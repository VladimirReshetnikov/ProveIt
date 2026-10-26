import NineCoordinatePackaging
import DiophantineConsistency.SplitSourceExistence
import DiophantineConsistency.GapSourceExistence66

/-!
PROPOSED COMPATIBILITY CHECKS, NOT COMPILED IN THIS REVIEW.
Keep the original public definitions and theorem statements; replace only
proof bodies by these applications after validating definitional equality.
The proposal file must be on Lean's import path, with its .olean built first.
-/

namespace DiophantineConsistency.NineCoordinatePackagingCompatibilityProposal

theorem split_positive (d : SplitSourceWords.Parameters) (a : ℕ) :
    (∃ x : Fin 9 → ℕ, (∀ i, 0 < x i) ∧
      SplitSourceExistence.positiveValue d a x = 0) ↔
        SplitSourceExistence.HasZero d a := by
  exact NineCoordinatePackagingProposal.exists_positive_zero_iff_hasZero (SplitSourceExistence.value d a)

theorem split_natural (d : SplitSourceWords.Parameters) (a : ℕ) :
    (∃ x : Fin 9 → ℕ, SplitSourceExistence.naturalValue d a x = 0) ↔
      SplitSourceExistence.HasZero d a := by
  exact NineCoordinatePackagingProposal.exists_natural_zero_iff_hasZero (SplitSourceExistence.value d a)

theorem gap_positive (d : GapSourceWords66.Parameters) (a : ℕ) :
    (∃ x : Fin 9 → ℕ, (∀ i, 0 < x i) ∧
      GapSourceExistence66.positiveValue d a x = 0) ↔
        GapSourceExistence66.HasZero d a := by
  exact NineCoordinatePackagingProposal.exists_positive_zero_iff_hasZero (GapSourceExistence66.value d a)

theorem gap_natural (d : GapSourceWords66.Parameters) (a : ℕ) :
    (∃ x : Fin 9 → ℕ, GapSourceExistence66.naturalValue d a x = 0) ↔
      GapSourceExistence66.HasZero d a := by
  exact NineCoordinatePackagingProposal.exists_natural_zero_iff_hasZero (GapSourceExistence66.value d a)

#print axioms DiophantineConsistency.NineCoordinatePackagingCompatibilityProposal.split_positive
#print axioms DiophantineConsistency.NineCoordinatePackagingCompatibilityProposal.split_natural
#print axioms DiophantineConsistency.NineCoordinatePackagingCompatibilityProposal.gap_positive
#print axioms DiophantineConsistency.NineCoordinatePackagingCompatibilityProposal.gap_natural

end DiophantineConsistency.NineCoordinatePackagingCompatibilityProposal
