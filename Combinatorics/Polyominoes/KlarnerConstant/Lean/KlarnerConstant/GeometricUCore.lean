import KlarnerConstant.GeometricPPartition

/-!
# Core infrastructure for the five-branch geometric recurrence for `U`

This module defines the strengthened marked frame and seed systems, together
with the finite marked convolution targets and their lossless encoders.
-/

namespace LeanProofs.KlarnerConstant

/-! ## The stronger marked frame -/

/-- A marked `U` frame is a `P` frame together with the one extra southwest
forbidden cell. -/
structure UFrame (P : Polyomino) (anchor : Cell) : Prop extends
    PFrame P anchor where
  southwest_not : pCell anchor (-1) (-1) ∉ P.cells

namespace GeometricUInternal

open OrientedTerritoryOccurrence

/-- The new forbidden offset in the first four strengthened branches really is
the southwest cell of the original marked frame.  Keeping this coordinate
bridge named avoids asking simplification to normalize a record projection,
an inverse orientation, and integer pair arithmetic simultaneously. -/
theorem clockwise_extra_forbidden_cell (anchor : Cell) :
    pCell anchor 0 0 + GridOrientation.clockwise.inv (-1, 1) =
      pCell anchor (-1) (-1) := by
  apply Prod.ext <;>
    dsimp [pCell, GridOrientation.clockwise] <;> omega

/-- In the full-rectangle branch, the additional `Z` exclusion is seen from
the middle seed through the anti-diagonal orientation. -/
theorem antiDiagonal_extra_forbidden_cell (anchor : Cell) :
    pCell anchor 0 1 + GridOrientation.antiDiagonal.inv (2, 1) =
      pCell anchor (-1) (-1) := by
  apply Prod.ext <;>
    dsimp [pCell, GridOrientation.antiDiagonal] <;> omega

theorem uFrame_of_occursAt {P : Polyomino} {anchor : Cell}
    (h : buiUPattern.OccursAt P.cells anchor) : UFrame P anchor := by
  refine {
    left_mem := ?_
    right_mem := ?_
    southLeft_not := ?_
    southRight_not := ?_
    southeast_not := ?_
    southwest_not := ?_ }
  · simpa [pCell] using h.1 (0, 0) (by simp [buiUPattern])
  · simpa [pCell] using h.1 (1, 0) (by simp [buiUPattern])
  · simpa [pCell] using h.2 (0, -1) (by simp [buiUPattern])
  · simpa [pCell] using h.2 (1, -1) (by simp [buiUPattern])
  · simpa [pCell] using h.2 (2, -1) (by simp [buiUPattern])
  · simpa [pCell] using h.2 (-1, -1) (by simp [buiUPattern])

/-! ## Strengthened versions of the five `P` seed systems -/

/-- First branch (`D*H`): the cell above the left endpoint is absent. -/
def uTopLeftAbsentSeeds {P : Polyomino} {anchor : Cell}
    (frame : UFrame P anchor) (h01 : pCell anchor 0 1 ∉ P.cells) :
    PBranchSeeds 2 := by
  let base := pTopLeftAbsentSeeds frame.toPFrame h01
  refine { base with
    kinds := fun i ↦ if i = 0 then .d else .h
    required_mem := ?_
    forbidden_avoided := ?_ }
  · intro i offset hoffset
    fin_cases i
    · apply base.required_mem 0 offset
      simpa [base, pTopLeftAbsentSeeds, BuiNeighborhood.pattern,
        buiDPattern, buiEPattern] using hoffset
    · apply base.required_mem 1 offset
      simpa [base, pTopLeftAbsentSeeds, BuiNeighborhood.pattern,
        buiHPattern] using hoffset
  · intro i offset hoffset
    fin_cases i
    · simp [BuiNeighborhood.pattern, buiDPattern] at hoffset
      rcases hoffset with rfl | rfl | rfl | rfl | rfl | rfl
      · apply Or.inl
        change pCell anchor 0 0 +
          GridOrientation.clockwise.inv (-1, 1) ∉ P.cells
        rw [clockwise_extra_forbidden_cell]
        exact frame.southwest_not
      · exact base.forbidden_avoided 0 _
          (by simp [base, pTopLeftAbsentSeeds,
            BuiNeighborhood.pattern, buiEPattern])
      · exact base.forbidden_avoided 0 _
          (by simp [base, pTopLeftAbsentSeeds,
            BuiNeighborhood.pattern, buiEPattern])
      · exact base.forbidden_avoided 0 _
          (by simp [base, pTopLeftAbsentSeeds,
            BuiNeighborhood.pattern, buiEPattern])
      · exact base.forbidden_avoided 0 _
          (by simp [base, pTopLeftAbsentSeeds,
            BuiNeighborhood.pattern, buiEPattern])
      · exact base.forbidden_avoided 0 _
          (by simp [base, pTopLeftAbsentSeeds,
            BuiNeighborhood.pattern, buiEPattern])
    · exact base.forbidden_avoided 1 offset
        (by simpa [base, pTopLeftAbsentSeeds,
          BuiNeighborhood.pattern, buiHPattern] using hoffset)

/-- Second branch (`S*D`): only the upper-left cell of the second row is
present. -/
def uTopLeftOnlySeeds {P : Polyomino} {anchor : Cell}
    (frame : UFrame P anchor)
    (h01 : pCell anchor 0 1 ∈ P.cells)
    (h11 : pCell anchor 1 1 ∉ P.cells) : PBranchSeeds 2 := by
  let base := pTopLeftOnlySeeds frame.toPFrame h01 h11
  refine { base with
    kinds := fun i ↦ if i = 0 then .s else .d
    required_mem := ?_
    forbidden_avoided := ?_ }
  · intro i offset hoffset
    fin_cases i
    · apply base.required_mem 0 offset
      simpa [base, pTopLeftOnlySeeds, BuiNeighborhood.pattern,
        buiSPattern, buiQPattern] using hoffset
    · apply base.required_mem 1 offset
      simpa [base, pTopLeftOnlySeeds, BuiNeighborhood.pattern,
        buiDPattern] using hoffset
  · intro i offset hoffset
    fin_cases i
    · simp [BuiNeighborhood.pattern, buiSPattern] at hoffset
      rcases hoffset with rfl | rfl | rfl | rfl | rfl
      · apply Or.inl
        change pCell anchor 0 0 +
          GridOrientation.clockwise.inv (-1, 1) ∉ P.cells
        rw [clockwise_extra_forbidden_cell]
        exact frame.southwest_not
      · exact base.forbidden_avoided 0 _
          (by simp [base, pTopLeftOnlySeeds,
            BuiNeighborhood.pattern, buiQPattern])
      · exact base.forbidden_avoided 0 _
          (by simp [base, pTopLeftOnlySeeds,
            BuiNeighborhood.pattern, buiQPattern])
      · exact base.forbidden_avoided 0 _
          (by simp [base, pTopLeftOnlySeeds,
            BuiNeighborhood.pattern, buiQPattern])
      · exact base.forbidden_avoided 0 _
          (by simp [base, pTopLeftOnlySeeds,
            BuiNeighborhood.pattern, buiQPattern])
    · exact base.forbidden_avoided 1 offset
        (by simpa [base, pTopLeftOnlySeeds,
          BuiNeighborhood.pattern, buiDPattern] using hoffset)

/-- Third branch (`Y*R`): the first two rows are full, while the cell above
the left column is absent.  The first territory is deliberately anchored at
the lower cell and rotated clockwise. -/
def uFirstColumnSeeds {P : Polyomino} {anchor : Cell}
    (frame : UFrame P anchor)
    (h01 : pCell anchor 0 1 ∈ P.cells)
    (h11 : pCell anchor 1 1 ∈ P.cells)
    (h02 : pCell anchor 0 2 ∉ P.cells) : PBranchSeeds 2 := by
  let base := pFirstColumnSeeds frame.toPFrame h01 h11 h02
  refine { base with
    kinds := fun i ↦ if i = 0 then .y else .r
    orientations := fun i ↦
      if i = 0 then GridOrientation.clockwise else GridOrientation.diagonal
    physicalAnchors := fun i ↦
      if i = 0 then pCell anchor 0 0 else pCell anchor 1 0
    physicalAnchor_mem := ?_
    required_mem := ?_
    forbidden_avoided := ?_ }
  · intro i
    fin_cases i
    · simp [base, pFirstColumnSeeds]
    · simp [base, pFirstColumnSeeds, frame.right_mem]
  · intro i offset hoffset
    fin_cases i
    · simp [BuiNeighborhood.pattern, buiYPattern] at hoffset
      rcases hoffset with rfl | rfl <;>
        simp [base, pFirstColumnSeeds, GridOrientation.clockwise, pCell]
    · apply base.required_mem 1 offset
      simpa [base, pFirstColumnSeeds, BuiNeighborhood.pattern,
        buiRPattern] using hoffset
  · intro i offset hoffset
    fin_cases i
    · simp [BuiNeighborhood.pattern, buiYPattern] at hoffset
      rcases hoffset with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · apply Or.inl
        change pCell anchor 0 0 +
          GridOrientation.clockwise.inv (-1, 1) ∉ P.cells
        rw [clockwise_extra_forbidden_cell]
        exact frame.southwest_not
      · exact Or.inl (by
          simpa [base, pFirstColumnSeeds, pCell_add_clockwise_inv,
            add_offset_eq_pCell]
            using frame.southLeft_not)
      · exact Or.inl (by
          simpa [base, pFirstColumnSeeds, pCell_add_clockwise_inv,
            add_offset_eq_pCell]
            using h02)
      · exact Or.inl (by
          simpa [base, pFirstColumnSeeds, pCell_add_clockwise_inv,
            add_offset_eq_pCell]
            using frame.southRight_not)
      · exact Or.inr ⟨1, by decide, by
          simp [base, pFirstColumnSeeds, pCell_add_clockwise_inv,
            add_offset_eq_pCell, frame.right_mem]⟩
      · exact Or.inr ⟨1, by decide, by
          simp [base, pFirstColumnSeeds, pCell_add_clockwise_inv,
            add_offset_eq_pCell, h11]⟩
      · by_cases h12 : pCell anchor 1 2 ∈ P.cells
        · exact Or.inr ⟨1, by decide, by
            simp [base, pFirstColumnSeeds, pCell_add_clockwise_inv,
              add_offset_eq_pCell, h12]⟩
        · exact Or.inl (by
            simpa [base, pFirstColumnSeeds, pCell_add_clockwise_inv,
              add_offset_eq_pCell]
              using h12)
    · exact base.forbidden_avoided 1 offset
        (by simpa [base, pFirstColumnSeeds,
          BuiNeighborhood.pattern, buiRPattern] using hoffset)

/-- Fourth branch (`W*Y`): the left column has height three and the upper
right cell is absent. -/
def uFirstColumnTopRightSeeds {P : Polyomino} {anchor : Cell}
    (frame : UFrame P anchor)
    (h01 : pCell anchor 0 1 ∈ P.cells)
    (h02 : pCell anchor 0 2 ∈ P.cells)
    (h11 : pCell anchor 1 1 ∈ P.cells)
    (h12 : pCell anchor 1 2 ∉ P.cells) : PBranchSeeds 2 := by
  let base := pFirstColumnTopRightSeeds frame.toPFrame h01 h02 h11 h12
  refine { base with
    kinds := fun i ↦ if i = 0 then .w else .y
    required_mem := ?_
    forbidden_avoided := ?_ }
  · intro i offset hoffset
    fin_cases i
    · apply base.required_mem 0 offset
      simpa [base, pFirstColumnTopRightSeeds, BuiNeighborhood.pattern,
        buiWPattern, buiVPattern] using hoffset
    · apply base.required_mem 1 offset
      simpa [base, pFirstColumnTopRightSeeds, BuiNeighborhood.pattern,
        buiYPattern] using hoffset
  · intro i offset hoffset
    fin_cases i
    · simp [BuiNeighborhood.pattern, buiWPattern] at hoffset
      rcases hoffset with rfl | rfl | rfl | rfl | rfl | rfl
      · apply Or.inl
        change pCell anchor 0 0 +
          GridOrientation.clockwise.inv (-1, 1) ∉ P.cells
        rw [clockwise_extra_forbidden_cell]
        exact frame.southwest_not
      · exact base.forbidden_avoided 0 _
          (by simp [base, pFirstColumnTopRightSeeds,
            BuiNeighborhood.pattern, buiVPattern])
      · exact base.forbidden_avoided 0 _
          (by simp [base, pFirstColumnTopRightSeeds,
            BuiNeighborhood.pattern, buiVPattern])
      · exact base.forbidden_avoided 0 _
          (by simp [base, pFirstColumnTopRightSeeds,
            BuiNeighborhood.pattern, buiVPattern])
      · exact base.forbidden_avoided 0 _
          (by simp [base, pFirstColumnTopRightSeeds,
            BuiNeighborhood.pattern, buiVPattern])
      · exact base.forbidden_avoided 0 _
          (by simp [base, pFirstColumnTopRightSeeds,
            BuiNeighborhood.pattern, buiVPattern])
    · exact base.forbidden_avoided 1 offset
        (by simpa [base, pFirstColumnTopRightSeeds,
          BuiNeighborhood.pattern, buiYPattern] using hoffset)

/-- Fifth branch (`U*Z*Z`): all six cells are present.  The additional
southwest exclusion strengthens the middle `Y` territory to `Z`. -/
def uFullRectangleSeeds {P : Polyomino} {anchor : Cell}
    (frame : UFrame P anchor)
    (h01 : pCell anchor 0 1 ∈ P.cells)
    (h02 : pCell anchor 0 2 ∈ P.cells)
    (h11 : pCell anchor 1 1 ∈ P.cells)
    (h12 : pCell anchor 1 2 ∈ P.cells) : PBranchSeeds 3 := by
  let base := pFullRectangleSeeds frame.toPFrame h01 h02 h11 h12
  refine { base with
    kinds := fun i ↦ if i = 0 then .u else .z
    required_mem := ?_
    forbidden_avoided := ?_ }
  · intro i offset hoffset
    fin_cases i
    · apply base.required_mem 0 offset
      simpa [base, pFullRectangleSeeds,
        BuiNeighborhood.pattern, buiUPattern] using hoffset
    · apply base.required_mem 1 offset
      simpa [base, pFullRectangleSeeds, BuiNeighborhood.pattern,
        buiZPattern, buiYPattern] using hoffset
    · apply base.required_mem 2 offset
      simpa [base, pFullRectangleSeeds,
        BuiNeighborhood.pattern, buiZPattern] using hoffset
  · intro i offset hoffset
    fin_cases i
    · exact base.forbidden_avoided 0 offset
        (by simpa [base, pFullRectangleSeeds,
          BuiNeighborhood.pattern, buiUPattern] using hoffset)
    · simp [BuiNeighborhood.pattern, buiZPattern] at hoffset
      rcases hoffset with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact base.forbidden_avoided 1 _
          (by simp [base, pFullRectangleSeeds,
            BuiNeighborhood.pattern, buiYPattern])
      · apply Or.inl
        change pCell anchor 0 1 +
          GridOrientation.antiDiagonal.inv (2, 1) ∉ P.cells
        rw [antiDiagonal_extra_forbidden_cell]
        exact frame.southwest_not
      · exact base.forbidden_avoided 1 _
          (by simp [base, pFullRectangleSeeds,
            BuiNeighborhood.pattern, buiYPattern])
      · exact base.forbidden_avoided 1 _
          (by simp [base, pFullRectangleSeeds,
            BuiNeighborhood.pattern, buiYPattern])
      · exact base.forbidden_avoided 1 _
          (by simp [base, pFullRectangleSeeds,
            BuiNeighborhood.pattern, buiYPattern])
      · exact base.forbidden_avoided 1 _
          (by simp [base, pFullRectangleSeeds,
            BuiNeighborhood.pattern, buiYPattern])
      · exact base.forbidden_avoided 1 _
          (by simp [base, pFullRectangleSeeds,
            BuiNeighborhood.pattern, buiYPattern])
      · exact base.forbidden_avoided 1 _
          (by simp [base, pFullRectangleSeeds,
            BuiNeighborhood.pattern, buiYPattern])
    · exact base.forbidden_avoided 2 offset
        (by simpa [base, pFullRectangleSeeds,
          BuiNeighborhood.pattern, buiZPattern] using hoffset)

/-! ## Finite convolution targets and lossless encoders -/

abbrev UAntidiagonalIndex (n : ℕ) :=
  {ij : ℕ × ℕ // ij ∈ Finset.Nat.instHasAntidiagonal.antidiagonal n}

abbrev UMarkedPair
    (left right : BuiNeighborhood) (n : ℕ) :=
  Σ ij : UAntidiagonalIndex n,
    MarkedOccurrence left ij.1.1 × MarkedOccurrence right ij.1.2

abbrev UMarkedTriple
    (first second third : BuiNeighborhood) (n : ℕ) :=
  Σ outer : UAntidiagonalIndex n,
    UMarkedPair first second outer.1.1 ×
      MarkedOccurrence third outer.1.2

noncomputable def uEncodeTwo {n : ℕ}
    (D : PBranchSeeds 2) (hcard : D.polyomino.cells.card = n) :
    UMarkedPair (D.kinds 0) (D.kinds 1) n := by
  let a := (D.partition.territories 0).card
  let b := (D.partition.territories 1).card
  have hsum : a + b = n := by
    calc
      a + b = D.polyomino.cells.card := D.twoOutput_indices.2.2
      _ = n := hcard
  exact ⟨⟨(a, b), Finset.HasAntidiagonal.mem_antidiagonal.mpr hsum⟩,
    D.twoOutput⟩

noncomputable def uEncodeThree {n : ℕ}
    (D : PBranchSeeds 3) (hcard : D.polyomino.cells.card = n) :
    UMarkedTriple (D.kinds 0) (D.kinds 1) (D.kinds 2) n := by
  let a := (D.partition.territories 0).card
  let b := (D.partition.territories 1).card
  let c := (D.partition.territories 2).card
  have hsum : (a + b) + c = n := by
    calc
      (a + b) + c = D.polyomino.cells.card := D.threeOutput_indices.2.2.2
      _ = n := hcard
  refine ⟨⟨(a + b, c),
    Finset.HasAntidiagonal.mem_antidiagonal.mpr hsum⟩, ?_, D.threeOutput.2.2⟩
  exact ⟨⟨(a, b), Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩,
    D.threeOutput.1, D.threeOutput.2.1⟩

def recoverUMarkedPair {left right : BuiNeighborhood} {n : ℕ}
    (leftOrientation : GridOrientation) (leftOffset : Cell)
    (rightOrientation : GridOrientation) (rightOffset : Cell)
    (out : UMarkedPair left right n) : Finset Cell :=
  recoverMarkedTerritory leftOrientation leftOffset out.2.1 ∪
    recoverMarkedTerritory rightOrientation rightOffset out.2.2

def recoverUMarkedTriple
    {first second third : BuiNeighborhood} {n : ℕ}
    (firstOrientation : GridOrientation) (firstOffset : Cell)
    (secondOrientation : GridOrientation) (secondOffset : Cell)
    (thirdOrientation : GridOrientation) (thirdOffset : Cell)
    (out : UMarkedTriple first second third n) : Finset Cell :=
  recoverUMarkedPair firstOrientation firstOffset
      secondOrientation secondOffset out.2.1 ∪
    recoverMarkedTerritory thirdOrientation thirdOffset out.2.2

theorem recover_uEncodeTwo {n : ℕ}
    (D : PBranchSeeds 2) (hcard : D.polyomino.cells.card = n)
    (leftOffset rightOffset : Cell)
    (hleft : D.physicalAnchors 0 = D.anchor + leftOffset)
    (hright : D.physicalAnchors 1 = D.anchor + rightOffset) :
    recoverUMarkedPair (D.orientations 0) leftOffset
        (D.orientations 1) rightOffset (uEncodeTwo D hcard) =
      D.anchoredSourceCells := by
  classical
  change
    recoverMarkedTerritory (D.orientations 0) leftOffset
        (D.territoryOccurrence 0).toMarkedOccurrence ∪
      recoverMarkedTerritory (D.orientations 1) rightOffset
        (D.territoryOccurrence 1).toMarkedOccurrence = _
  have hrecoverLeft :
      recoverMarkedTerritory (D.orientations 0) leftOffset
          (D.territoryOccurrence 0).toMarkedOccurrence =
        (D.territoryOccurrence 0).territory.cells.image
          (fun c ↦ -D.anchor + c) := by
    have horientation :
        (D.territoryOccurrence 0).orientation = D.orientations 0 := rfl
    rw [← horientation]
    have hphysical :
        (D.territoryOccurrence 0).physicalAnchor = D.anchor + leftOffset := by
      change D.physicalAnchors 0 = D.anchor + leftOffset
      exact hleft
    exact OrientedTerritoryOccurrence.recover_toMarkedOccurrence
      (D.territoryOccurrence 0) D.anchor leftOffset hphysical
  have hrecoverRight :
      recoverMarkedTerritory (D.orientations 1) rightOffset
          (D.territoryOccurrence 1).toMarkedOccurrence =
        (D.territoryOccurrence 1).territory.cells.image
          (fun c ↦ -D.anchor + c) := by
    have horientation :
        (D.territoryOccurrence 1).orientation = D.orientations 1 := rfl
    rw [← horientation]
    have hphysical :
        (D.territoryOccurrence 1).physicalAnchor = D.anchor + rightOffset := by
      change D.physicalAnchors 1 = D.anchor + rightOffset
      exact hright
    exact OrientedTerritoryOccurrence.recover_toMarkedOccurrence
      (D.territoryOccurrence 1) D.anchor rightOffset hphysical
  rw [hrecoverLeft, hrecoverRight]
  rw [← D.anchored_cover]
  ext cell
  constructor
  · intro hcell
    rcases Finset.mem_union.mp hcell with hcell | hcell
    · exact mem_coveredCells.mpr ⟨0, hcell⟩
    · exact mem_coveredCells.mpr ⟨1, hcell⟩
  · intro hcell
    rcases mem_coveredCells.mp hcell with ⟨i, hi⟩
    fin_cases i
    · exact Finset.mem_union.mpr (Or.inl hi)
    · exact Finset.mem_union.mpr (Or.inr hi)

theorem recover_uEncodeThree {n : ℕ}
    (D : PBranchSeeds 3) (hcard : D.polyomino.cells.card = n)
    (firstOffset secondOffset thirdOffset : Cell)
    (hfirst : D.physicalAnchors 0 = D.anchor + firstOffset)
    (hsecond : D.physicalAnchors 1 = D.anchor + secondOffset)
    (hthird : D.physicalAnchors 2 = D.anchor + thirdOffset) :
    recoverUMarkedTriple (D.orientations 0) firstOffset
        (D.orientations 1) secondOffset
        (D.orientations 2) thirdOffset (uEncodeThree D hcard) =
      D.anchoredSourceCells := by
  classical
  change
    (recoverMarkedTerritory (D.orientations 0) firstOffset
        (D.territoryOccurrence 0).toMarkedOccurrence ∪
      recoverMarkedTerritory (D.orientations 1) secondOffset
        (D.territoryOccurrence 1).toMarkedOccurrence) ∪
      recoverMarkedTerritory (D.orientations 2) thirdOffset
        (D.territoryOccurrence 2).toMarkedOccurrence = _
  have hrecoverFirst :
      recoverMarkedTerritory (D.orientations 0) firstOffset
          (D.territoryOccurrence 0).toMarkedOccurrence =
        (D.territoryOccurrence 0).territory.cells.image
          (fun c ↦ -D.anchor + c) := by
    have horientation :
        (D.territoryOccurrence 0).orientation = D.orientations 0 := rfl
    rw [← horientation]
    have hphysical :
        (D.territoryOccurrence 0).physicalAnchor = D.anchor + firstOffset := by
      change D.physicalAnchors 0 = D.anchor + firstOffset
      exact hfirst
    exact OrientedTerritoryOccurrence.recover_toMarkedOccurrence
      (D.territoryOccurrence 0) D.anchor firstOffset hphysical
  have hrecoverSecond :
      recoverMarkedTerritory (D.orientations 1) secondOffset
          (D.territoryOccurrence 1).toMarkedOccurrence =
        (D.territoryOccurrence 1).territory.cells.image
          (fun c ↦ -D.anchor + c) := by
    have horientation :
        (D.territoryOccurrence 1).orientation = D.orientations 1 := rfl
    rw [← horientation]
    have hphysical :
        (D.territoryOccurrence 1).physicalAnchor = D.anchor + secondOffset := by
      change D.physicalAnchors 1 = D.anchor + secondOffset
      exact hsecond
    exact OrientedTerritoryOccurrence.recover_toMarkedOccurrence
      (D.territoryOccurrence 1) D.anchor secondOffset hphysical
  have hrecoverThird :
      recoverMarkedTerritory (D.orientations 2) thirdOffset
          (D.territoryOccurrence 2).toMarkedOccurrence =
        (D.territoryOccurrence 2).territory.cells.image
          (fun c ↦ -D.anchor + c) := by
    have horientation :
        (D.territoryOccurrence 2).orientation = D.orientations 2 := rfl
    rw [← horientation]
    have hphysical :
        (D.territoryOccurrence 2).physicalAnchor = D.anchor + thirdOffset := by
      change D.physicalAnchors 2 = D.anchor + thirdOffset
      exact hthird
    exact OrientedTerritoryOccurrence.recover_toMarkedOccurrence
      (D.territoryOccurrence 2) D.anchor thirdOffset hphysical
  rw [hrecoverFirst, hrecoverSecond, hrecoverThird]
  rw [← D.anchored_cover]
  ext cell
  constructor
  · intro hcell
    rcases Finset.mem_union.mp hcell with hcell | hcell
    · rcases Finset.mem_union.mp hcell with hcell | hcell
      · exact mem_coveredCells.mpr ⟨0, hcell⟩
      · exact mem_coveredCells.mpr ⟨1, hcell⟩
    · exact mem_coveredCells.mpr ⟨2, hcell⟩
  · intro hcell
    rcases mem_coveredCells.mp hcell with ⟨i, hi⟩
    fin_cases i
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hi)))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hi)))
    · exact Finset.mem_union.mpr (Or.inr hi)


end GeometricUInternal

end LeanProofs.KlarnerConstant
