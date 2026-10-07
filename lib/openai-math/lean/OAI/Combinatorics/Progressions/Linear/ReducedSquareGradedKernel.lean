import OAI.Combinatorics.Progressions.Estimates.GradedUnitEvaluation

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

theorem quotientTopGradedMap_piece (j : ℕ) (x : F.layer j) :
    F.quotientTopGradedMap (F.associatedGradedPieceMap j x) =
      F.quotientTop.associatedGradedPieceMap j
        ⟨lieQuotientMap (F.layerIdeal (s + 1)) x,
          F.quotientLie_mem (F.layerIdeal (s + 1)) (t := s) le_rfl x.property⟩ :=
  F.quotientGradedMap_piece (F.layerIdeal (s + 1)) (t := s) le_rfl j x

theorem reducedSquareGradedSnd_piece (j : ℕ) (x : F.squareFiltration.layer j) :
    F.reducedSquareGradedSndMap
      (F.squareFiltration.quotientTopGradedMap (F.squareFiltration.associatedGradedPieceMap j x)) =
    F.quotientTopGradedMap (F.associatedGradedPieceMap j ⟨x.val.val.2, x.property.2.1⟩) := by
  simp only [reducedSquareGradedSndMap, quotientTopGradedMap]
  rfl

theorem reducedSquareGradedPiece_kernel_relative (j : ℕ) (hpos : 1 ≤ j) (hj : j ≤ s)
    (x : F.squareFiltration.layer j)
    (hx : F.reducedSquareGradedSndMap
      (F.squareFiltration.quotientTopGradedMap (F.squareFiltration.associatedGradedPieceMap j x)) = 0) :
    F.reducedSquareGradedRelativePiece j hpos ⟨x.val.val.1 - x.val.val.2, x.property.2.2⟩ =
      F.squareFiltration.quotientTopGradedMap (F.squareFiltration.associatedGradedPieceMap j x) := by
  rw [F.reducedSquareGradedSnd_piece] at hx
  have hsnd := (F.quotientTopGradedMap_piece_eq_zero_iff j hj _).mp hx
  have hd := (F.reducedSquareGradedDiagonalPiece_eq_zero_iff j hj
    ⟨x.val.val.2, x.property.2.1⟩).mpr hsnd
  have hdec := congrArg F.squareFiltration.quotientTopGradedMap
    (F.squareGradedPiece_decomposition j hpos x)
  rw [map_add] at hdec
  change _ = F.reducedSquareGradedDiagonalPiece j ⟨x.val.val.2, x.property.2.1⟩ +
    F.reducedSquareGradedRelativePiece j hpos ⟨x.val.val.1 - x.val.val.2, x.property.2.2⟩ at hdec
  rw [hd, zero_add] at hdec
  exact hdec.symm

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem exists_reducedSquareGradedRelativePiece_of_pure_kernel
    (j : ℕ) (hpos : 1 ≤ j) (hj : j ≤ s)
    (y : F.squareFiltration.quotientTop.AssociatedGraded)
    (hy : basisGradeProjection bW ωW j y = y) (hker : F.reducedSquareGradedSndMap y = 0) :
    ∃ x : F.layer (j + 1), F.reducedSquareGradedRelativePiece j hpos x = y := by
  obtain ⟨q, hq⟩ := F.squareFiltration.quotientTop.exists_associatedGradedPieceMap_of_pure
    (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) j y hy
  obtain ⟨x, hx, hxq⟩ := q.property
  have he : F.squareFiltration.quotientTopGradedMap
      (F.squareFiltration.associatedGradedPieceMap j ⟨x, hx⟩) = y := by
    rw [F.squareFiltration.quotientTopGradedMap_piece]
    refine Eq.trans ?_ hq
    apply congrArg (F.squareFiltration.quotientTop.associatedGradedPieceMap j)
    exact Subtype.ext hxq
  refine ⟨⟨x.val.1 - x.val.2, hx.2.2⟩, ?_⟩
  exact (F.reducedSquareGradedPiece_kernel_relative j hpos hj ⟨x, hx⟩
    (by rw [he]; exact hker)).trans he

theorem reducedSquareGradedDifference_relativePiece (j : ℕ) (hj : 1 ≤ j)
    (x : F.layer (j + 1)) :
    F.reducedSquareGradedDifference e ω hF (F.reducedSquareGradedRelativePiece j hj x) =
      F.associatedGradedPieceMap (j + 1) x := by
  change F.reducedSquareGradedDifference e ω hF
    (F.squareFiltration.quotientTopGradedMap
      (F.squareFiltration.associatedGradedPieceMap j (F.squareRelativeLayer j hj x))) = _
  rw [F.squareFiltration.quotientTopGradedMap_piece,
    ← F.squareFiltration.quotientTop.gradedPieceProjection_eq_pieceMap
      (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)]
  rw [F.reducedSquareGradedDifference_projection, F.reducedSquareDifference_mk]
  change F.gradedPieceProjection e ω hF (j + 1) ((x : L) - 0) = _
  rw [sub_zero, F.gradedPieceProjection_eq_pieceMap]

end Erdos3.NilpotentLieFiltration

end

end OAI
