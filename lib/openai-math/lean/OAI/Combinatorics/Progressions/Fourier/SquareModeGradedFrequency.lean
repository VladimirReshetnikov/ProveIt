import OAI.Combinatorics.Progressions.Estimates.CommonNativeSquareFactors
import OAI.Combinatorics.Progressions.Estimates.FastGradedRelativeInvariance
import OAI.Combinatorics.Progressions.Linear.ReducedSquareGradedKernel

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "δ" => F.reducedSquareGradedDifference e ω hF

theorem fullFastGradedRelative_top_frequency (hs : 1 ≤ s)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (ξ : F.squareFiltration.quotientTop.AssociatedGraded →ₗ[ℚ] ℚ)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (hrestriction : ∀ x : F.layer (s + 1),
      ξ (F.reducedSquareGradedRelativePiece s hs x) = η (F.associatedGradedPieceMap (s + 1) x))
    (hξ : ∀ y ∈ W, basisGradeProjection bW ωW s y = y → ξ y = 0) :
    ∀ x ∈ F.fullFastGradedRelative e ω hF W,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) x = x → η x = 0 := by
  rintro x ⟨y, hy, rfl⟩ hpure
  let ys := basisGradeProjection bW ωW s y
  have hys : ys ∈ F.fastGradedRelativeKernel W :=
    F.fastGradedRelativeKernel_graded e ω hF W hW s y hy
  have hysPure : basisGradeProjection bW ωW s ys = ys :=
    basisCoordinateProjection_idempotent bW {i | ωW i = s} y
  have hδ : δ ys = δ y := (F.reducedSquareGradedDifference_gradeProjection e ω hF s y).trans hpure
  obtain ⟨z, hz⟩ := F.exists_reducedSquareGradedRelativePiece_of_pure_kernel e ω hF
    s hs le_rfl ys hysPure hys.2
  calc
    η (δ y) = η (δ ys) := congrArg η hδ.symm
    _ = η (δ (F.reducedSquareGradedRelativePiece s hs z)) :=
      congrArg (fun u => η (δ u)) hz.symm
    _ = η (F.associatedGradedPieceMap (s + 1) z) :=
      congrArg η (F.reducedSquareGradedDifference_relativePiece e ω hF s hs z)
    _ = ξ (F.reducedSquareGradedRelativePiece s hs z) := (hrestriction z).symm
    _ = ξ ys := congrArg ξ hz
    _ = 0 := hξ ys hys.1 hysPure

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

local notation "bq" => F.reducedSquareBasis b ω hF
local notation "ωq" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "hq" => F.reducedSquareBasis_layers b ω hF
local notation "bG" => F.squareFiltration.quotientTop.associatedGradedBasis bq ωq hq

theorem square_gradedFrequency_restriction (hs : 1 ≤ s)
    (η : L →ₗ[ℚ] ℚ)
    (ξ : (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
    (hrestriction : ∀ x : F.layer (s + 1),
      ξ (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
        (F.squareRelativeLayer s hs x).val) = η x)
    (x : F.layer (s + 1)) :
    F.squareFiltration.quotientTop.gradedFrequency bq ωq hq ξ
        (F.reducedSquareGradedRelativePiece s hs x) =
      F.gradedFrequency b ω hF η (F.associatedGradedPieceMap (s + 1) x) := by
  change F.squareFiltration.quotientTop.gradedFrequency bq ωq hq ξ
    (F.squareFiltration.quotientTopGradedMap
      (F.squareFiltration.associatedGradedPieceMap s (F.squareRelativeLayer s hs x))) = _
  rw [F.squareFiltration.quotientTopGradedMap_piece,
    F.squareFiltration.quotientTop.gradedFrequency_top_piece,
    F.gradedFrequency_top_piece]
  exact hrestriction x

theorem square_mode_fullFast_top_frequency (hs : 1 ≤ s)
    (η : L →ₗ[ℚ] ℚ)
    (ξ : (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
    (hrestriction : ∀ x : F.layer (s + 1),
      ξ (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
        (F.squareRelativeLayer s hs x).val) = η x)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bG ωq W.toSubmodule)
    (hξ : ∀ y ∈ W, basisGradeProjection bG ωq s y = y →
      F.squareFiltration.quotientTop.gradedFrequency bq ωq hq ξ y = 0) :
    ∀ x ∈ F.fullFastGradedRelative b ω hF W,
      basisGradeProjection (F.associatedGradedBasis b ω hF) ω (s + 1) x = x →
        F.gradedFrequency b ω hF η x = 0 := by
  exact F.fullFastGradedRelative_top_frequency b ω hF hs W hW
    (F.squareFiltration.quotientTop.gradedFrequency bq ωq hq ξ)
    (F.gradedFrequency b ω hF η)
    (F.square_gradedFrequency_restriction b ω hF hs η ξ hrestriction) hξ

end Erdos3.NilpotentLieFiltration

end

end OAI
