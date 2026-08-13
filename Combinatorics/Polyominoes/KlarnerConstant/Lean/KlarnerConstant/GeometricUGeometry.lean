import KlarnerConstant.GeometricUCore

/-!
# Branch geometry for the five-branch `U` recurrence

This module constructs the five marked branch maps and proves lossless
reconstruction and injectivity for each branch.
-/

namespace LeanProofs.KlarnerConstant

namespace GeometricUInternal

/-! ## Concrete branch maps -/

private theorem uMem_occurrenceAnchors_iff (pattern : OffsetPattern)
    (cells : Finset Cell) (anchor : Cell) :
    anchor ∈ pattern.occurrenceAnchors cells ↔
      anchor ∈ cells ∧ pattern.OccursAt cells anchor := by
  classical
  rw [OffsetPattern.occurrenceAnchors, Finset.mem_filter]

theorem uMarked_occursAt {n : ℕ} (x : MarkedOccurrence .u n) :
    buiUPattern.OccursAt x.1.toPolyomino.cells x.2.1 := by
  exact ((uMem_occurrenceAnchors_iff _ _ _).1 x.2.2).2

def uAnchoredCells {n : ℕ} (x : MarkedOccurrence .u n) :
    Finset Cell :=
  x.1.toPolyomino.cells.image fun c ↦ -x.2.1 + c

noncomputable def uFirstMap {n : ℕ} (x : MarkedOccurrence .u n)
    (frame : UFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∉ x.1.toPolyomino.cells) :
    UMarkedPair .d .h n := by
  let D := uTopLeftAbsentSeeds frame h01
  change UMarkedPair (D.kinds 0) (D.kinds 1) n
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  exact uEncodeTwo D hcard

noncomputable def uSecondMap {n : ℕ} (x : MarkedOccurrence .u n)
    (frame : UFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h11 : pCell x.2.1 1 1 ∉ x.1.toPolyomino.cells) :
    UMarkedPair .s .d n := by
  let D := uTopLeftOnlySeeds frame h01 h11
  change UMarkedPair (D.kinds 0) (D.kinds 1) n
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  exact uEncodeTwo D hcard

noncomputable def uThirdMap {n : ℕ} (x : MarkedOccurrence .u n)
    (frame : UFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h11 : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells)
    (h02 : pCell x.2.1 0 2 ∉ x.1.toPolyomino.cells) :
    UMarkedPair .y .r n := by
  let D := uFirstColumnSeeds frame h01 h11 h02
  change UMarkedPair (D.kinds 0) (D.kinds 1) n
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  exact uEncodeTwo D hcard

noncomputable def uFourthMap {n : ℕ} (x : MarkedOccurrence .u n)
    (frame : UFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h02 : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells)
    (h11 : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells)
    (h12 : pCell x.2.1 1 2 ∉ x.1.toPolyomino.cells) :
    UMarkedPair .w .y n := by
  let D := uFirstColumnTopRightSeeds frame h01 h02 h11 h12
  change UMarkedPair (D.kinds 0) (D.kinds 1) n
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  exact uEncodeTwo D hcard

noncomputable def uFifthMap {n : ℕ} (x : MarkedOccurrence .u n)
    (frame : UFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h02 : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells)
    (h11 : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells)
    (h12 : pCell x.2.1 1 2 ∈ x.1.toPolyomino.cells) :
    UMarkedTriple .u .z .z n := by
  let D := uFullRectangleSeeds frame h01 h02 h11 h12
  change UMarkedTriple (D.kinds 0) (D.kinds 1) (D.kinds 2) n
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  exact uEncodeThree D hcard

/-! ## Reconstruction and branchwise injectivity -/

theorem uFirst_reconstruct {n : ℕ} (x : MarkedOccurrence .u n)
    (frame : UFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∉ x.1.toPolyomino.cells) :
    recoverUMarkedPair GridOrientation.clockwise (0, 0)
        GridOrientation.identity (1, 0) (uFirstMap x frame h01) =
      uAnchoredCells x := by
  let D := uTopLeftAbsentSeeds frame h01
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  have hrecover := recover_uEncodeTwo D
    hcard (0, 0) (1, 0)
    (by rfl)
    (by rfl)
  have hleftOrientation :
      D.orientations 0 = GridOrientation.clockwise := by rfl
  have hrightOrientation :
      D.orientations 1 = GridOrientation.identity := by rfl
  have hmap : uFirstMap x frame h01 = uEncodeTwo D hcard := by
    change uEncodeTwo D (hcard := hcard) = uEncodeTwo D hcard
    rfl
  have hsource : D.anchoredSourceCells = uAnchoredCells x := by
    have hpolyomino : D.polyomino = x.1.toPolyomino := by rfl
    have hanchor : D.anchor = x.2.1 := by rfl
    unfold PBranchSeeds.anchoredSourceCells uAnchoredCells
    rw [hpolyomino, hanchor]
  calc
    _ = recoverUMarkedPair (D.orientations 0) (0, 0)
        (D.orientations 1) (1, 0) (uEncodeTwo D hcard) := by
      rw [hleftOrientation, hrightOrientation, hmap]
      rfl
    _ = D.anchoredSourceCells := hrecover
    _ = uAnchoredCells x := hsource

theorem uSecond_reconstruct {n : ℕ} (x : MarkedOccurrence .u n)
    (frame : UFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h11 : pCell x.2.1 1 1 ∉ x.1.toPolyomino.cells) :
    recoverUMarkedPair GridOrientation.clockwise (0, 0)
        GridOrientation.diagonal (1, 0) (uSecondMap x frame h01 h11) =
      uAnchoredCells x := by
  let D := uTopLeftOnlySeeds frame h01 h11
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  have hrecover := recover_uEncodeTwo D
    hcard (0, 0) (1, 0)
    (by rfl)
    (by rfl)
  have hleftOrientation :
      D.orientations 0 = GridOrientation.clockwise := by rfl
  have hrightOrientation :
      D.orientations 1 = GridOrientation.diagonal := by rfl
  have hmap : uSecondMap x frame h01 h11 = uEncodeTwo D hcard := by
    change uEncodeTwo D (hcard := hcard) = uEncodeTwo D hcard
    rfl
  have hsource : D.anchoredSourceCells = uAnchoredCells x := by
    have hpolyomino : D.polyomino = x.1.toPolyomino := by rfl
    have hanchor : D.anchor = x.2.1 := by rfl
    unfold PBranchSeeds.anchoredSourceCells uAnchoredCells
    rw [hpolyomino, hanchor]
  calc
    _ = recoverUMarkedPair (D.orientations 0) (0, 0)
        (D.orientations 1) (1, 0) (uEncodeTwo D hcard) := by
      rw [hleftOrientation, hrightOrientation, hmap]
      rfl
    _ = D.anchoredSourceCells := hrecover
    _ = uAnchoredCells x := hsource

theorem uThird_reconstruct {n : ℕ} (x : MarkedOccurrence .u n)
    (frame : UFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h11 : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells)
    (h02 : pCell x.2.1 0 2 ∉ x.1.toPolyomino.cells) :
    recoverUMarkedPair GridOrientation.clockwise (0, 0)
        GridOrientation.diagonal (1, 0) (uThirdMap x frame h01 h11 h02) =
      uAnchoredCells x := by
  let D := uFirstColumnSeeds frame h01 h11 h02
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  have hrecover := recover_uEncodeTwo D
    hcard (0, 0) (1, 0)
    (by rfl)
    (by rfl)
  have hleftOrientation :
      D.orientations 0 = GridOrientation.clockwise := by rfl
  have hrightOrientation :
      D.orientations 1 = GridOrientation.diagonal := by rfl
  have hmap : uThirdMap x frame h01 h11 h02 = uEncodeTwo D hcard := by
    change uEncodeTwo D (hcard := hcard) = uEncodeTwo D hcard
    rfl
  have hsource : D.anchoredSourceCells = uAnchoredCells x := by
    have hpolyomino : D.polyomino = x.1.toPolyomino := by rfl
    have hanchor : D.anchor = x.2.1 := by rfl
    unfold PBranchSeeds.anchoredSourceCells uAnchoredCells
    rw [hpolyomino, hanchor]
  calc
    _ = recoverUMarkedPair (D.orientations 0) (0, 0)
        (D.orientations 1) (1, 0) (uEncodeTwo D hcard) := by
      rw [hleftOrientation, hrightOrientation, hmap]
      rfl
    _ = D.anchoredSourceCells := hrecover
    _ = uAnchoredCells x := hsource

theorem uFourth_reconstruct {n : ℕ} (x : MarkedOccurrence .u n)
    (frame : UFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h02 : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells)
    (h11 : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells)
    (h12 : pCell x.2.1 1 2 ∉ x.1.toPolyomino.cells) :
    recoverUMarkedPair GridOrientation.clockwise (0, 0)
        GridOrientation.diagonal (1, 0)
        (uFourthMap x frame h01 h02 h11 h12) =
      uAnchoredCells x := by
  let D := uFirstColumnTopRightSeeds frame h01 h02 h11 h12
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  have hrecover := recover_uEncodeTwo D
    hcard (0, 0) (1, 0)
    (by rfl)
    (by rfl)
  have hleftOrientation :
      D.orientations 0 = GridOrientation.clockwise := by rfl
  have hrightOrientation :
      D.orientations 1 = GridOrientation.diagonal := by rfl
  have hmap : uFourthMap x frame h01 h02 h11 h12 = uEncodeTwo D hcard := by
    change uEncodeTwo D (hcard := hcard) = uEncodeTwo D hcard
    rfl
  have hsource : D.anchoredSourceCells = uAnchoredCells x := by
    have hpolyomino : D.polyomino = x.1.toPolyomino := by rfl
    have hanchor : D.anchor = x.2.1 := by rfl
    unfold PBranchSeeds.anchoredSourceCells uAnchoredCells
    rw [hpolyomino, hanchor]
  calc
    _ = recoverUMarkedPair (D.orientations 0) (0, 0)
        (D.orientations 1) (1, 0) (uEncodeTwo D hcard) := by
      rw [hleftOrientation, hrightOrientation, hmap]
      rfl
    _ = D.anchoredSourceCells := hrecover
    _ = uAnchoredCells x := hsource

theorem uFifth_reconstruct {n : ℕ} (x : MarkedOccurrence .u n)
    (frame : UFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h02 : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells)
    (h11 : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells)
    (h12 : pCell x.2.1 1 2 ∈ x.1.toPolyomino.cells) :
    recoverUMarkedTriple GridOrientation.identity (0, 2)
        GridOrientation.antiDiagonal (0, 1)
        GridOrientation.diagonal (1, 0)
        (uFifthMap x frame h01 h02 h11 h12) =
      uAnchoredCells x := by
  let D := uFullRectangleSeeds frame h01 h02 h11 h12
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  have hrecover := recover_uEncodeThree D
    hcard (0, 2) (0, 1) (1, 0)
    (by rfl)
    (by rfl)
    (by rfl)
  have hfirstOrientation :
      D.orientations 0 = GridOrientation.identity := by rfl
  have hsecondOrientation :
      D.orientations 1 = GridOrientation.antiDiagonal := by rfl
  have hthirdOrientation :
      D.orientations 2 = GridOrientation.diagonal := by rfl
  have hmap :
      uFifthMap x frame h01 h02 h11 h12 = uEncodeThree D hcard := by
    change uEncodeThree D (hcard := hcard) = uEncodeThree D hcard
    rfl
  have hsource : D.anchoredSourceCells = uAnchoredCells x := by
    have hpolyomino : D.polyomino = x.1.toPolyomino := by rfl
    have hanchor : D.anchor = x.2.1 := by rfl
    unfold PBranchSeeds.anchoredSourceCells uAnchoredCells
    rw [hpolyomino, hanchor]
  calc
    _ = recoverUMarkedTriple (D.orientations 0) (0, 2)
        (D.orientations 1) (0, 1)
        (D.orientations 2) (1, 0) (uEncodeThree D hcard) := by
      rw [hfirstOrientation, hsecondOrientation, hthirdOrientation, hmap]
      rfl
    _ = D.anchoredSourceCells := hrecover
    _ = uAnchoredCells x := hsource

theorem uFirstMap_injective {n : ℕ}
    (x y : MarkedOccurrence .u n)
    (fx : UFrame x.1.toPolyomino x.2.1)
    (fy : UFrame y.1.toPolyomino y.2.1)
    (hx : pCell x.2.1 0 1 ∉ x.1.toPolyomino.cells)
    (hy : pCell y.2.1 0 1 ∉ y.1.toPolyomino.cells)
    (hmap : uFirstMap x fx hx = uFirstMap y fy hy) : x = y := by
  apply normalized_marked_source_injective
  have h := congrArg (recoverUMarkedPair GridOrientation.clockwise (0, 0)
    GridOrientation.identity (1, 0)) hmap
  rw [uFirst_reconstruct x fx hx, uFirst_reconstruct y fy hy] at h
  exact h

theorem uSecondMap_injective {n : ℕ}
    (x y : MarkedOccurrence .u n)
    (fx : UFrame x.1.toPolyomino x.2.1)
    (fy : UFrame y.1.toPolyomino y.2.1)
    (h01x : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h01y : pCell y.2.1 0 1 ∈ y.1.toPolyomino.cells)
    (h11x : pCell x.2.1 1 1 ∉ x.1.toPolyomino.cells)
    (h11y : pCell y.2.1 1 1 ∉ y.1.toPolyomino.cells)
    (hmap : uSecondMap x fx h01x h11x =
      uSecondMap y fy h01y h11y) : x = y := by
  apply normalized_marked_source_injective
  have h := congrArg (recoverUMarkedPair GridOrientation.clockwise (0, 0)
    GridOrientation.diagonal (1, 0)) hmap
  rw [uSecond_reconstruct x fx h01x h11x,
    uSecond_reconstruct y fy h01y h11y] at h
  exact h

theorem uThirdMap_injective {n : ℕ}
    (x y : MarkedOccurrence .u n)
    (fx : UFrame x.1.toPolyomino x.2.1)
    (fy : UFrame y.1.toPolyomino y.2.1)
    (h01x : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h01y : pCell y.2.1 0 1 ∈ y.1.toPolyomino.cells)
    (h11x : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells)
    (h11y : pCell y.2.1 1 1 ∈ y.1.toPolyomino.cells)
    (h02x : pCell x.2.1 0 2 ∉ x.1.toPolyomino.cells)
    (h02y : pCell y.2.1 0 2 ∉ y.1.toPolyomino.cells)
    (hmap : uThirdMap x fx h01x h11x h02x =
      uThirdMap y fy h01y h11y h02y) : x = y := by
  apply normalized_marked_source_injective
  have h := congrArg (recoverUMarkedPair GridOrientation.clockwise (0, 0)
    GridOrientation.diagonal (1, 0)) hmap
  rw [uThird_reconstruct x fx h01x h11x h02x,
    uThird_reconstruct y fy h01y h11y h02y] at h
  exact h

theorem uFourthMap_injective {n : ℕ}
    (x y : MarkedOccurrence .u n)
    (fx : UFrame x.1.toPolyomino x.2.1)
    (fy : UFrame y.1.toPolyomino y.2.1)
    (h01x : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h01y : pCell y.2.1 0 1 ∈ y.1.toPolyomino.cells)
    (h02x : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells)
    (h02y : pCell y.2.1 0 2 ∈ y.1.toPolyomino.cells)
    (h11x : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells)
    (h11y : pCell y.2.1 1 1 ∈ y.1.toPolyomino.cells)
    (h12x : pCell x.2.1 1 2 ∉ x.1.toPolyomino.cells)
    (h12y : pCell y.2.1 1 2 ∉ y.1.toPolyomino.cells)
    (hmap : uFourthMap x fx h01x h02x h11x h12x =
      uFourthMap y fy h01y h02y h11y h12y) : x = y := by
  apply normalized_marked_source_injective
  have h := congrArg (recoverUMarkedPair GridOrientation.clockwise (0, 0)
    GridOrientation.diagonal (1, 0)) hmap
  rw [uFourth_reconstruct x fx h01x h02x h11x h12x,
    uFourth_reconstruct y fy h01y h02y h11y h12y] at h
  exact h

theorem uFifthMap_injective {n : ℕ}
    (x y : MarkedOccurrence .u n)
    (fx : UFrame x.1.toPolyomino x.2.1)
    (fy : UFrame y.1.toPolyomino y.2.1)
    (h01x : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h01y : pCell y.2.1 0 1 ∈ y.1.toPolyomino.cells)
    (h02x : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells)
    (h02y : pCell y.2.1 0 2 ∈ y.1.toPolyomino.cells)
    (h11x : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells)
    (h11y : pCell y.2.1 1 1 ∈ y.1.toPolyomino.cells)
    (h12x : pCell x.2.1 1 2 ∈ x.1.toPolyomino.cells)
    (h12y : pCell y.2.1 1 2 ∈ y.1.toPolyomino.cells)
    (hmap : uFifthMap x fx h01x h02x h11x h12x =
      uFifthMap y fy h01y h02y h11y h12y) : x = y := by
  apply normalized_marked_source_injective
  have h := congrArg (recoverUMarkedTriple GridOrientation.identity (0, 2)
    GridOrientation.antiDiagonal (0, 1)
    GridOrientation.diagonal (1, 0)) hmap
  rw [uFifth_reconstruct x fx h01x h02x h11x h12x,
    uFifth_reconstruct y fy h01y h02y h11y h12y] at h
  exact h


end GeometricUInternal

end LeanProofs.KlarnerConstant
