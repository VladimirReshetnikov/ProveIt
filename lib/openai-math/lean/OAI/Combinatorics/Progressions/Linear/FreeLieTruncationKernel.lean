import OAI.Combinatorics.Progressions.Nilpotent.FreeNilpotentLieAlgebra
import OAI.Combinatorics.Progressions.Nilpotent.WordTruncationBracket

namespace OAI

section

namespace Erdos3

variable {X : Type*}

theorem freeLieTruncation_eq_zero_iff (s : ℕ) (p : FreeLieAlgebra ℚ X) :
    freeLieTruncation s p = 0 ↔
      p ∈ LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s := by
  constructor
  · intro hp
    apply (FreeNilpotentLieAlgebra.mk_eq_zero X s p).mp
    rw [← FreeNilpotentLieAlgebra.mk_truncation p, hp, map_zero]
  · exact freeLie_lowerCentralSeries_truncation_zero s p

theorem freeLieTruncation_ker (s : ℕ) :
    LinearMap.ker (freeLieTruncation (X := X) s) =
      (LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s).toSubmodule := by
  ext p
  exact freeLieTruncation_eq_zero_iff s p

theorem freeLie_lowerCentralSeries_iff_low_coeff_zero (s : ℕ) (p : FreeLieAlgebra ℚ X) :
    p ∈ LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s ↔
      ∀ w, w.length ≤ s → (freeLieWordExpansion p).coeff w = 0 := by
  rw [← freeLieTruncation_eq_zero_iff, ← wordTruncation_eq_zero_iff]
  constructor
  · intro hp
    rw [← freeLieTruncation_expansion, hp, map_zero]
  · intro hp
    apply freeLieWordExpansion_injective
    rw [freeLieTruncation_expansion, hp, map_zero]

end Erdos3

end

end OAI
