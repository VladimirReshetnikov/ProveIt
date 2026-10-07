import OAI.Combinatorics.Progressions.Fourier.CommonCoveredSiteCharacter

namespace OAI

section

namespace Erdos3

variable {J I E : Type*} [Fintype J] [Fintype I] [Fintype E]

theorem standardLatticeSection_basis_card_eq
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)]
    (o : OrthonormalBasis I ℝ W)
    (bW : Module.Basis E ℤ (latticeSection (standardEuclideanLattice J) W)) :
    Fintype.card E = Fintype.card I := by
  rw [← Module.finrank_eq_card_basis bW, ZLattice.rank ℝ,
    Module.finrank_eq_card_basis o.toBasis]

theorem preparedDeckBasis_card_eq
    (U : Submodule ℝ (J → ℝ))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) (euclideanSubspace U))]
    (o : OrthonormalBasis I ℝ (euclideanSubspace U))
    (bW : Module.Basis E ℤ (latticeSection (standardEuclideanLattice J) (euclideanSubspace U))) :
    Fintype.card E = Fintype.card I :=
  standardLatticeSection_basis_card_eq (euclideanSubspace U) o bW

end Erdos3

end

end OAI
