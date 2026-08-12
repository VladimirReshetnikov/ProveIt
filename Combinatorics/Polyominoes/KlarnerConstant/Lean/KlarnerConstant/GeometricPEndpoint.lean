import KlarnerConstant.GeometricPGeometry

/-!
# Finite encoding and coefficient endpoint for the `P` recurrence

This module maps every marked `P` occurrence into the appropriate two- or
three-factor positive Cauchy-product target, proves the map injective by
reconstruction, and exports the public aggregate and coefficient
recurrence theorems.
-/

namespace LeanProofs.KlarnerConstant

open OrientedTerritoryOccurrence

/-! ## Finite convolution targets -/

private abbrev PAntidiagonalIndex (n : ℕ) :=
  {ij : ℕ × ℕ //
    ij ∈ Finset.Nat.instHasAntidiagonal.antidiagonal n}

private abbrev PMarkedPair
    (left right : BuiNeighborhood) (n : ℕ) :=
  Σ ij : PAntidiagonalIndex n,
    MarkedOccurrence left ij.1.1 × MarkedOccurrence right ij.1.2

/-- A left-associated three-factor target, matching the definition
`cauchyThree a b c = cauchyTwo (cauchyTwo a b) c`. -/
private abbrev PMarkedTriple
    (first second third : BuiNeighborhood) (n : ℕ) :=
  Σ outer : PAntidiagonalIndex n,
    PMarkedPair first second outer.1.1 ×
      MarkedOccurrence third outer.1.2

private theorem pAggregate_zero (kind : BuiNeighborhood) :
    kind.aggregateOccurrenceCount 0 = 0 := by
  classical
  unfold BuiNeighborhood.aggregateOccurrenceCount
  apply Finset.sum_eq_zero
  intro P _
  have hpos : 0 < P.toPolyomino.cells.card :=
    Finset.card_pos.mpr P.toPolyomino.nonempty
  rw [P.card_cells] at hpos
  omega

private theorem pCard_markedOccurrence (kind : BuiNeighborhood) (n : ℕ) :
    Fintype.card (MarkedOccurrence kind n) =
      kind.aggregateOccurrenceCount n := by
  classical
  simp [MarkedOccurrence, BuiNeighborhood.aggregateOccurrenceCount,
    BuiNeighborhood.occurrenceCount, OffsetPattern.occurrenceCount]

private noncomputable def pPositiveAggregate (kind : BuiNeighborhood) : ℕ → ℕ
  | 0 => 0
  | n + 1 => kind.aggregateOccurrenceCount (n + 1)

private theorem pCard_markedOccurrence_eq_positiveAggregate
    (kind : BuiNeighborhood) (n : ℕ) :
    Fintype.card (MarkedOccurrence kind n) = pPositiveAggregate kind n := by
  cases n with
  | zero =>
      rw [pCard_markedOccurrence, pAggregate_zero]
      rfl
  | succ n =>
      rw [pCard_markedOccurrence]
      rfl

/-- Natural-number cardinal of the positive-index two-factor marked target. -/
noncomputable def buiPairAggregateCount
    (left right : BuiNeighborhood) (n : ℕ) : ℕ :=
  ∑ ij ∈ Finset.Nat.instHasAntidiagonal.antidiagonal n,
    pPositiveAggregate left ij.1 * pPositiveAggregate right ij.2

/-- Natural-number cardinal of the positive-index left-associated
three-factor marked target. -/
noncomputable def buiTripleAggregateCount
    (first second third : BuiNeighborhood) (n : ℕ) : ℕ :=
  ∑ outer ∈ Finset.Nat.instHasAntidiagonal.antidiagonal n,
    buiPairAggregateCount first second outer.1 *
      pPositiveAggregate third outer.2

private theorem pCard_markedPair
    (left right : BuiNeighborhood) (n : ℕ) :
    Fintype.card (PMarkedPair left right n) =
      buiPairAggregateCount left right n := by
  classical
  change Fintype.card
      (Σ ij : PAntidiagonalIndex n,
        MarkedOccurrence left ij.1.1 × MarkedOccurrence right ij.1.2) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod,
    pCard_markedOccurrence_eq_positiveAggregate]
  rw [Finset.univ_eq_attach
    (Finset.Nat.instHasAntidiagonal.antidiagonal n)]
  unfold buiPairAggregateCount
  exact Finset.sum_attach
    (Finset.Nat.instHasAntidiagonal.antidiagonal n)
    (fun ij => pPositiveAggregate left ij.1 * pPositiveAggregate right ij.2)

private theorem pCard_markedTriple
    (first second third : BuiNeighborhood) (n : ℕ) :
    Fintype.card (PMarkedTriple first second third n) =
      buiTripleAggregateCount first second third n := by
  classical
  change Fintype.card
      (Σ outer : PAntidiagonalIndex n,
        PMarkedPair first second outer.1.1 ×
          MarkedOccurrence third outer.1.2) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod,
    pCard_markedPair, pCard_markedOccurrence_eq_positiveAggregate]
  rw [Finset.univ_eq_attach
    (Finset.Nat.instHasAntidiagonal.antidiagonal n)]
  unfold buiTripleAggregateCount
  exact Finset.sum_attach
    (Finset.Nat.instHasAntidiagonal.antidiagonal n)
    (fun outer => buiPairAggregateCount first second outer.1 *
      pPositiveAggregate third outer.2)

theorem cauchyTwo_coefficient_eq_buiPairAggregateCount
    (left right : BuiNeighborhood) (n : ℕ) :
    cauchyTwo left.coefficient right.coefficient n =
      (buiPairAggregateCount left right n : ℚ) := by
  classical
  unfold cauchyTwo buiPairAggregateCount BuiNeighborhood.coefficient
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [Nat.cast_mul]
  congr 1
  · cases ij.1 <;> simp [positivePart, pPositiveAggregate]
  · cases ij.2 <;> simp [positivePart, pPositiveAggregate]

theorem cauchyThree_coefficient_eq_buiTripleAggregateCount
    (first second third : BuiNeighborhood) (n : ℕ) :
    cauchyThree first.coefficient second.coefficient third.coefficient n =
      (buiTripleAggregateCount first second third n : ℚ) := by
  classical
  change (∑ outer ∈ Finset.Nat.instHasAntidiagonal.antidiagonal n,
      positivePart (cauchyTwo first.coefficient second.coefficient) outer.1 *
        positivePart third.coefficient outer.2) = _
  unfold buiTripleAggregateCount
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro outer houter
  rw [Nat.cast_mul]
  congr 1
  · cases outer.1 with
    | zero => simp [positivePart, buiPairAggregateCount, pPositiveAggregate]
    | succ m =>
        simp only [positivePart_succ]
        exact cauchyTwo_coefficient_eq_buiPairAggregateCount first second (m + 1)
  · cases outer.2 <;>
      simp [positivePart, pPositiveAggregate, BuiNeighborhood.coefficient]

/-! ## Lossless branch encoders -/

private noncomputable def PBranchSeeds.encodeTwo {n : ℕ}
    (D : PBranchSeeds 2) (hcard : D.polyomino.cells.card = n) :
    PMarkedPair (D.kinds 0) (D.kinds 1) n := by
  let a := (D.partition.territories 0).card
  let b := (D.partition.territories 1).card
  have hsum : a + b = n := by
    calc
      a + b = D.polyomino.cells.card := D.twoOutput_indices.2.2
      _ = n := hcard
  exact ⟨⟨(a, b), Finset.HasAntidiagonal.mem_antidiagonal.mpr hsum⟩,
    D.twoOutput⟩

private noncomputable def PBranchSeeds.encodeThree {n : ℕ}
    (D : PBranchSeeds 3) (hcard : D.polyomino.cells.card = n) :
    PMarkedTriple (D.kinds 0) (D.kinds 1) (D.kinds 2) n := by
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

private def recoverPMarkedPair {left right : BuiNeighborhood} {n : ℕ}
    (leftOrientation : GridOrientation) (leftOffset : Cell)
    (rightOrientation : GridOrientation) (rightOffset : Cell)
    (out : PMarkedPair left right n) : Finset Cell :=
  recoverMarkedTerritory leftOrientation leftOffset out.2.1 ∪
    recoverMarkedTerritory rightOrientation rightOffset out.2.2

private def recoverPMarkedTriple
    {first second third : BuiNeighborhood} {n : ℕ}
    (firstOrientation : GridOrientation) (firstOffset : Cell)
    (secondOrientation : GridOrientation) (secondOffset : Cell)
    (thirdOrientation : GridOrientation) (thirdOffset : Cell)
    (out : PMarkedTriple first second third n) : Finset Cell :=
  recoverPMarkedPair firstOrientation firstOffset
      secondOrientation secondOffset out.2.1 ∪
    recoverMarkedTerritory thirdOrientation thirdOffset out.2.2

/-- A projection-stable form of `recover_toMarkedOccurrence` for one
territory selected by branch data.  Naming this bridge avoids asking `rw` to
unfold the tactic-defined `territoryOccurrence` while matching its orientation
projection. -/
private theorem PBranchSeeds.recover_territoryOccurrence {k : ℕ}
    (D : PBranchSeeds k) (i : Fin k) (offset : Cell)
    (hphysical : D.physicalAnchors i = D.anchor + offset) :
    recoverMarkedTerritory (D.orientations i) offset
        (D.territoryOccurrence i).toMarkedOccurrence =
      (D.partition.territories i).image (fun c ↦ -D.anchor + c) := by
  have hrecover :=
    OrientedTerritoryOccurrence.recover_toMarkedOccurrence
      (D.territoryOccurrence i) D.anchor offset (by
        change D.physicalAnchors i = D.anchor + offset
        exact hphysical)
  change recoverMarkedTerritory (D.orientations i) offset
      (D.territoryOccurrence i).toMarkedOccurrence =
    (D.partition.territories i).image (fun c ↦ -D.anchor + c) at hrecover
  exact hrecover

private theorem PBranchSeeds.recover_encodeTwo {n : ℕ}
    (D : PBranchSeeds 2) (hcard : D.polyomino.cells.card = n)
    (leftOffset rightOffset : Cell)
    (hleft : D.physicalAnchors 0 = D.anchor + leftOffset)
    (hright : D.physicalAnchors 1 = D.anchor + rightOffset) :
    recoverPMarkedPair (D.orientations 0) leftOffset
        (D.orientations 1) rightOffset (D.encodeTwo hcard) =
      D.anchoredSourceCells := by
  classical
  change
    recoverMarkedTerritory (D.orientations 0) leftOffset
        (D.territoryOccurrence 0).toMarkedOccurrence ∪
      recoverMarkedTerritory (D.orientations 1) rightOffset
        (D.territoryOccurrence 1).toMarkedOccurrence = _
  rw [D.recover_territoryOccurrence 0 leftOffset hleft,
    D.recover_territoryOccurrence 1 rightOffset hright]
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

private theorem PBranchSeeds.recover_encodeThree {n : ℕ}
    (D : PBranchSeeds 3) (hcard : D.polyomino.cells.card = n)
    (firstOffset secondOffset thirdOffset : Cell)
    (hfirst : D.physicalAnchors 0 = D.anchor + firstOffset)
    (hsecond : D.physicalAnchors 1 = D.anchor + secondOffset)
    (hthird : D.physicalAnchors 2 = D.anchor + thirdOffset) :
    recoverPMarkedTriple (D.orientations 0) firstOffset
        (D.orientations 1) secondOffset
        (D.orientations 2) thirdOffset (D.encodeThree hcard) =
      D.anchoredSourceCells := by
  classical
  change
    (recoverMarkedTerritory (D.orientations 0) firstOffset
        (D.territoryOccurrence 0).toMarkedOccurrence ∪
      recoverMarkedTerritory (D.orientations 1) secondOffset
        (D.territoryOccurrence 1).toMarkedOccurrence) ∪
      recoverMarkedTerritory (D.orientations 2) thirdOffset
        (D.territoryOccurrence 2).toMarkedOccurrence = _
  rw [D.recover_territoryOccurrence 0 firstOffset hfirst,
    D.recover_territoryOccurrence 1 secondOffset hsecond,
    D.recover_territoryOccurrence 2 thirdOffset hthird]
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

/-! ## The five concrete marked branch maps -/

private theorem pMem_occurrenceAnchors_iff (pattern : OffsetPattern)
    (cells : Finset Cell) (anchor : Cell) :
    anchor ∈ pattern.occurrenceAnchors cells ↔
      anchor ∈ cells ∧ pattern.OccursAt cells anchor := by
  classical
  rw [OffsetPattern.occurrenceAnchors, Finset.mem_filter]

private theorem pMarked_occursAt {n : ℕ} (x : MarkedOccurrence .p n) :
    buiPPattern.OccursAt x.1.toPolyomino.cells x.2.1 := by
  exact ((pMem_occurrenceAnchors_iff _ _ _).1 x.2.2).2

private def pAnchoredCells {n : ℕ} (x : MarkedOccurrence .p n) :
    Finset Cell :=
  x.1.toPolyomino.cells.image fun c ↦ -x.2.1 + c

private noncomputable def pFirstMap {n : ℕ} (x : MarkedOccurrence .p n)
    (frame : PFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∉ x.1.toPolyomino.cells) :
    PMarkedPair .e .h n := by
  let D := pTopLeftAbsentSeeds frame h01
  change PMarkedPair (D.kinds 0) (D.kinds 1) n
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  exact D.encodeTwo hcard

private noncomputable def pSecondMap {n : ℕ} (x : MarkedOccurrence .p n)
    (frame : PFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h11 : pCell x.2.1 1 1 ∉ x.1.toPolyomino.cells) :
    PMarkedPair .q .d n := by
  let D := pTopLeftOnlySeeds frame h01 h11
  change PMarkedPair (D.kinds 0) (D.kinds 1) n
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  exact D.encodeTwo hcard

private noncomputable def pThirdMap {n : ℕ} (x : MarkedOccurrence .p n)
    (frame : PFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h11 : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells)
    (h02 : pCell x.2.1 0 2 ∉ x.1.toPolyomino.cells) :
    PMarkedPair .x .r n := by
  let D := pFirstColumnSeeds frame h01 h11 h02
  change PMarkedPair (D.kinds 0) (D.kinds 1) n
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  exact D.encodeTwo hcard

private noncomputable def pFourthMap {n : ℕ} (x : MarkedOccurrence .p n)
    (frame : PFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h02 : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells)
    (h11 : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells)
    (h12 : pCell x.2.1 1 2 ∉ x.1.toPolyomino.cells) :
    PMarkedPair .v .y n := by
  let D := pFirstColumnTopRightSeeds frame h01 h02 h11 h12
  change PMarkedPair (D.kinds 0) (D.kinds 1) n
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  exact D.encodeTwo hcard

private noncomputable def pFifthMap {n : ℕ} (x : MarkedOccurrence .p n)
    (frame : PFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h02 : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells)
    (h11 : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells)
    (h12 : pCell x.2.1 1 2 ∈ x.1.toPolyomino.cells) :
    PMarkedTriple .u .y .z n := by
  let D := pFullRectangleSeeds frame h01 h02 h11 h12
  change PMarkedTriple (D.kinds 0) (D.kinds 1) (D.kinds 2) n
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  exact D.encodeThree hcard

/-! ## Branch reconstruction and injectivity -/

private theorem pFirst_reconstruct {n : ℕ} (x : MarkedOccurrence .p n)
    (frame : PFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∉ x.1.toPolyomino.cells) :
    recoverPMarkedPair GridOrientation.clockwise (0, 0)
        GridOrientation.identity (1, 0) (pFirstMap x frame h01) =
      pAnchoredCells x := by
  let D := pTopLeftAbsentSeeds frame h01
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  have hrecover := D.recover_encodeTwo
    hcard (0, 0) (1, 0)
    (by rfl)
    (by rfl)
  simpa [pFirstMap, D, pTopLeftAbsentSeeds, pAnchoredCells,
    PBranchSeeds.anchoredSourceCells] using hrecover

private theorem pSecond_reconstruct {n : ℕ} (x : MarkedOccurrence .p n)
    (frame : PFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h11 : pCell x.2.1 1 1 ∉ x.1.toPolyomino.cells) :
    recoverPMarkedPair GridOrientation.clockwise (0, 0)
        GridOrientation.diagonal (1, 0) (pSecondMap x frame h01 h11) =
      pAnchoredCells x := by
  let D := pTopLeftOnlySeeds frame h01 h11
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  have hrecover := D.recover_encodeTwo
    hcard (0, 0) (1, 0)
    (by rfl)
    (by rfl)
  simpa [pSecondMap, D, pTopLeftOnlySeeds, pAnchoredCells,
    PBranchSeeds.anchoredSourceCells] using hrecover

private theorem pThird_reconstruct {n : ℕ} (x : MarkedOccurrence .p n)
    (frame : PFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h11 : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells)
    (h02 : pCell x.2.1 0 2 ∉ x.1.toPolyomino.cells) :
    recoverPMarkedPair GridOrientation.antiDiagonal (0, 1)
        GridOrientation.diagonal (1, 0) (pThirdMap x frame h01 h11 h02) =
      pAnchoredCells x := by
  let D := pFirstColumnSeeds frame h01 h11 h02
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  have hrecover := D.recover_encodeTwo
    hcard (0, 1) (1, 0)
    (by rfl)
    (by rfl)
  simpa [pThirdMap, D, pFirstColumnSeeds, pAnchoredCells,
    PBranchSeeds.anchoredSourceCells] using hrecover

private theorem pFourth_reconstruct {n : ℕ} (x : MarkedOccurrence .p n)
    (frame : PFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h02 : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells)
    (h11 : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells)
    (h12 : pCell x.2.1 1 2 ∉ x.1.toPolyomino.cells) :
    recoverPMarkedPair GridOrientation.clockwise (0, 0)
        GridOrientation.diagonal (1, 0)
        (pFourthMap x frame h01 h02 h11 h12) =
      pAnchoredCells x := by
  let D := pFirstColumnTopRightSeeds frame h01 h02 h11 h12
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  have hrecover := D.recover_encodeTwo
    hcard (0, 0) (1, 0)
    (by rfl)
    (by rfl)
  simpa [pFourthMap, D, pFirstColumnTopRightSeeds, pAnchoredCells,
    PBranchSeeds.anchoredSourceCells] using hrecover

private theorem pFifth_reconstruct {n : ℕ} (x : MarkedOccurrence .p n)
    (frame : PFrame x.1.toPolyomino x.2.1)
    (h01 : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h02 : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells)
    (h11 : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells)
    (h12 : pCell x.2.1 1 2 ∈ x.1.toPolyomino.cells) :
    recoverPMarkedTriple GridOrientation.identity (0, 2)
        GridOrientation.antiDiagonal (0, 1)
        GridOrientation.diagonal (1, 0)
        (pFifthMap x frame h01 h02 h11 h12) =
      pAnchoredCells x := by
  let D := pFullRectangleSeeds frame h01 h02 h11 h12
  have hcard : D.polyomino.cells.card = n := by
    change x.1.toPolyomino.cells.card = n
    exact x.1.card_cells
  have hrecover := D.recover_encodeThree
    hcard (0, 2) (0, 1) (1, 0)
    (by rfl)
    (by rfl)
    (by rfl)
  simpa [pFifthMap, D, pFullRectangleSeeds, pAnchoredCells,
    PBranchSeeds.anchoredSourceCells] using hrecover

private theorem pFirstMap_injective {n : ℕ}
    (x y : MarkedOccurrence .p n)
    (fx : PFrame x.1.toPolyomino x.2.1)
    (fy : PFrame y.1.toPolyomino y.2.1)
    (hx : pCell x.2.1 0 1 ∉ x.1.toPolyomino.cells)
    (hy : pCell y.2.1 0 1 ∉ y.1.toPolyomino.cells)
    (hmap : pFirstMap x fx hx = pFirstMap y fy hy) : x = y := by
  apply normalized_marked_source_injective
  have h := congrArg (recoverPMarkedPair GridOrientation.clockwise (0, 0)
    GridOrientation.identity (1, 0)) hmap
  rw [pFirst_reconstruct x fx hx, pFirst_reconstruct y fy hy] at h
  exact h

private theorem pSecondMap_injective {n : ℕ}
    (x y : MarkedOccurrence .p n)
    (fx : PFrame x.1.toPolyomino x.2.1)
    (fy : PFrame y.1.toPolyomino y.2.1)
    (h01x : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h01y : pCell y.2.1 0 1 ∈ y.1.toPolyomino.cells)
    (h11x : pCell x.2.1 1 1 ∉ x.1.toPolyomino.cells)
    (h11y : pCell y.2.1 1 1 ∉ y.1.toPolyomino.cells)
    (hmap : pSecondMap x fx h01x h11x =
      pSecondMap y fy h01y h11y) : x = y := by
  apply normalized_marked_source_injective
  have h := congrArg (recoverPMarkedPair GridOrientation.clockwise (0, 0)
    GridOrientation.diagonal (1, 0)) hmap
  rw [pSecond_reconstruct x fx h01x h11x,
    pSecond_reconstruct y fy h01y h11y] at h
  exact h

private theorem pThirdMap_injective {n : ℕ}
    (x y : MarkedOccurrence .p n)
    (fx : PFrame x.1.toPolyomino x.2.1)
    (fy : PFrame y.1.toPolyomino y.2.1)
    (h01x : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h01y : pCell y.2.1 0 1 ∈ y.1.toPolyomino.cells)
    (h11x : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells)
    (h11y : pCell y.2.1 1 1 ∈ y.1.toPolyomino.cells)
    (h02x : pCell x.2.1 0 2 ∉ x.1.toPolyomino.cells)
    (h02y : pCell y.2.1 0 2 ∉ y.1.toPolyomino.cells)
    (hmap : pThirdMap x fx h01x h11x h02x =
      pThirdMap y fy h01y h11y h02y) : x = y := by
  apply normalized_marked_source_injective
  have h := congrArg (recoverPMarkedPair GridOrientation.antiDiagonal (0, 1)
    GridOrientation.diagonal (1, 0)) hmap
  rw [pThird_reconstruct x fx h01x h11x h02x,
    pThird_reconstruct y fy h01y h11y h02y] at h
  exact h

private theorem pFourthMap_injective {n : ℕ}
    (x y : MarkedOccurrence .p n)
    (fx : PFrame x.1.toPolyomino x.2.1)
    (fy : PFrame y.1.toPolyomino y.2.1)
    (h01x : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h01y : pCell y.2.1 0 1 ∈ y.1.toPolyomino.cells)
    (h02x : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells)
    (h02y : pCell y.2.1 0 2 ∈ y.1.toPolyomino.cells)
    (h11x : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells)
    (h11y : pCell y.2.1 1 1 ∈ y.1.toPolyomino.cells)
    (h12x : pCell x.2.1 1 2 ∉ x.1.toPolyomino.cells)
    (h12y : pCell y.2.1 1 2 ∉ y.1.toPolyomino.cells)
    (hmap : pFourthMap x fx h01x h02x h11x h12x =
      pFourthMap y fy h01y h02y h11y h12y) : x = y := by
  apply normalized_marked_source_injective
  have h := congrArg (recoverPMarkedPair GridOrientation.clockwise (0, 0)
    GridOrientation.diagonal (1, 0)) hmap
  rw [pFourth_reconstruct x fx h01x h02x h11x h12x,
    pFourth_reconstruct y fy h01y h02y h11y h12y] at h
  exact h

private theorem pFifthMap_injective {n : ℕ}
    (x y : MarkedOccurrence .p n)
    (fx : PFrame x.1.toPolyomino x.2.1)
    (fy : PFrame y.1.toPolyomino y.2.1)
    (h01x : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells)
    (h01y : pCell y.2.1 0 1 ∈ y.1.toPolyomino.cells)
    (h02x : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells)
    (h02y : pCell y.2.1 0 2 ∈ y.1.toPolyomino.cells)
    (h11x : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells)
    (h11y : pCell y.2.1 1 1 ∈ y.1.toPolyomino.cells)
    (h12x : pCell x.2.1 1 2 ∈ x.1.toPolyomino.cells)
    (h12y : pCell y.2.1 1 2 ∈ y.1.toPolyomino.cells)
    (hmap : pFifthMap x fx h01x h02x h11x h12x =
      pFifthMap y fy h01y h02y h11y h12y) : x = y := by
  apply normalized_marked_source_injective
  have h := congrArg (recoverPMarkedTriple GridOrientation.identity (0, 2)
    GridOrientation.antiDiagonal (0, 1)
    GridOrientation.diagonal (1, 0)) hmap
  rw [pFifth_reconstruct x fx h01x h02x h11x h12x,
    pFifth_reconstruct y fy h01y h02y h11y h12y] at h
  exact h

/-! ## The global five-way injection and the `P` recurrence -/

private abbrev PTarget (n : ℕ) :=
  Sum (PMarkedPair .e .h n)
    (Sum (PMarkedPair .q .d n)
      (Sum (PMarkedPair .x .r n)
        (Sum (PMarkedPair .v .y n)
          (PMarkedTriple .u .y .z n))))

private noncomputable def pMarkedMap (n : ℕ) :
    MarkedOccurrence .p n → PTarget n := fun x ↦ by
  let frame : PFrame x.1.toPolyomino x.2.1 :=
    pFrame_of_occursAt (pMarked_occursAt x)
  by_cases h01 : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells
  · by_cases h11 : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells
    · by_cases h02 : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells
      · by_cases h12 : pCell x.2.1 1 2 ∈ x.1.toPolyomino.cells
        · exact Sum.inr (Sum.inr (Sum.inr (Sum.inr
            (pFifthMap x frame h01 h02 h11 h12))))
        · exact Sum.inr (Sum.inr (Sum.inr (Sum.inl
            (pFourthMap x frame h01 h02 h11 h12))))
      · exact Sum.inr (Sum.inr (Sum.inl
          (pThirdMap x frame h01 h11 h02)))
    · exact Sum.inr (Sum.inl (pSecondMap x frame h01 h11))
  · exact Sum.inl (pFirstMap x frame h01)

private theorem pMarkedMap_injective (n : ℕ) :
    Function.Injective (pMarkedMap n) := by
  intro x y hxy
  let fx : PFrame x.1.toPolyomino x.2.1 :=
    pFrame_of_occursAt (pMarked_occursAt x)
  let fy : PFrame y.1.toPolyomino y.2.1 :=
    pFrame_of_occursAt (pMarked_occursAt y)
  by_cases h01x : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells
  · by_cases h01y : pCell y.2.1 0 1 ∈ y.1.toPolyomino.cells
    · by_cases h11x : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells
      · by_cases h11y : pCell y.2.1 1 1 ∈ y.1.toPolyomino.cells
        · by_cases h02x : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells
          · by_cases h02y : pCell y.2.1 0 2 ∈ y.1.toPolyomino.cells
            · by_cases h12x : pCell x.2.1 1 2 ∈ x.1.toPolyomino.cells
              · by_cases h12y : pCell y.2.1 1 2 ∈ y.1.toPolyomino.cells
                · apply pFifthMap_injective x y fx fy h01x h01y h02x h02y
                      h11x h11y h12x h12y
                  simpa [pMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                    h02x, h02y, h12x, h12y] using hxy
                · simp [pMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                    h02x, h02y, h12x, h12y] at hxy
              · by_cases h12y : pCell y.2.1 1 2 ∈ y.1.toPolyomino.cells
                · simp [pMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                    h02x, h02y, h12x, h12y] at hxy
                · apply pFourthMap_injective x y fx fy h01x h01y h02x h02y
                      h11x h11y h12x h12y
                  simpa [pMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                    h02x, h02y, h12x, h12y] using hxy
            · by_cases h12x :
                  pCell x.2.1 1 2 ∈ x.1.toPolyomino.cells
              · simp [pMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                  h02x, h02y, h12x] at hxy
              · simp [pMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                  h02x, h02y, h12x] at hxy
          · by_cases h02y : pCell y.2.1 0 2 ∈ y.1.toPolyomino.cells
            · by_cases h12y :
                  pCell y.2.1 1 2 ∈ y.1.toPolyomino.cells
              · simp [pMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                  h02x, h02y, h12y] at hxy
              · simp [pMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                  h02x, h02y, h12y] at hxy
            · apply pThirdMap_injective x y fx fy h01x h01y h11x h11y
                  h02x h02y
              simpa [pMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                h02x, h02y] using hxy
        · by_cases h02x : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells
          · by_cases h12x : pCell x.2.1 1 2 ∈ x.1.toPolyomino.cells
            · simp [pMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                h02x, h12x] at hxy
            · simp [pMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                h02x, h12x] at hxy
          · simp [pMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
              h02x] at hxy
      · by_cases h11y : pCell y.2.1 1 1 ∈ y.1.toPolyomino.cells
        · by_cases h02y : pCell y.2.1 0 2 ∈ y.1.toPolyomino.cells
          · by_cases h12y : pCell y.2.1 1 2 ∈ y.1.toPolyomino.cells
            · simp [pMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                h02y, h12y] at hxy
            · simp [pMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                h02y, h12y] at hxy
          · simp [pMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
              h02y] at hxy
        · apply pSecondMap_injective x y fx fy h01x h01y h11x h11y
          simpa [pMarkedMap, fx, fy, h01x, h01y, h11x, h11y] using hxy
    · by_cases h11x : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells
      · by_cases h02x : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells
        · by_cases h12x : pCell x.2.1 1 2 ∈ x.1.toPolyomino.cells
          · simp [pMarkedMap, fx, fy, h01x, h01y, h11x,
              h02x, h12x] at hxy
          · simp [pMarkedMap, fx, fy, h01x, h01y, h11x,
              h02x, h12x] at hxy
        · simp [pMarkedMap, fx, fy, h01x, h01y, h11x, h02x] at hxy
      · simp [pMarkedMap, fx, fy, h01x, h01y, h11x] at hxy
  · by_cases h01y : pCell y.2.1 0 1 ∈ y.1.toPolyomino.cells
    · by_cases h11y : pCell y.2.1 1 1 ∈ y.1.toPolyomino.cells
      · by_cases h02y : pCell y.2.1 0 2 ∈ y.1.toPolyomino.cells
        · by_cases h12y : pCell y.2.1 1 2 ∈ y.1.toPolyomino.cells
          · simp [pMarkedMap, fx, fy, h01x, h01y, h11y,
              h02y, h12y] at hxy
          · simp [pMarkedMap, fx, fy, h01x, h01y, h11y,
              h02y, h12y] at hxy
        · simp [pMarkedMap, fx, fy, h01x, h01y, h11y, h02y] at hxy
      · simp [pMarkedMap, fx, fy, h01x, h01y, h11y] at hxy
    · apply pFirstMap_injective x y fx fy h01x h01y
      simpa [pMarkedMap, fx, fy, h01x, h01y] using hxy

private theorem pCard_pTarget (n : ℕ) :
    Fintype.card (PTarget n) =
      buiPairAggregateCount .e .h n +
      buiPairAggregateCount .q .d n +
      buiPairAggregateCount .x .r n +
      buiPairAggregateCount .v .y n +
      buiTripleAggregateCount .u .y .z n := by
  simp only [PTarget, Fintype.card_sum, pCard_markedPair,
    pCard_markedTriple]
  omega

/-- The natural-number marked-occurrence form of Bui's five-branch `P`
recurrence, proved by a lossless finite geometric decomposition. -/
theorem buiP_aggregateOccurrenceCount_le (n : ℕ) :
    BuiNeighborhood.p.aggregateOccurrenceCount n ≤
      buiPairAggregateCount .e .h n +
      buiPairAggregateCount .q .d n +
      buiPairAggregateCount .x .r n +
      buiPairAggregateCount .v .y n +
      buiTripleAggregateCount .u .y .z n := by
  rw [← pCard_markedOccurrence, ← pCard_pTarget]
  exact Fintype.card_le_of_injective (pMarkedMap n) (pMarkedMap_injective n)

/-- The unconditional rational coefficient inequality for the actual
geometric `P` sequence. -/
theorem buiP_coefficient_le (n : ℕ) :
    BuiNeighborhood.p.coefficient n ≤
      cauchyTwo BuiNeighborhood.e.coefficient BuiNeighborhood.h.coefficient n +
      cauchyTwo BuiNeighborhood.q.coefficient BuiNeighborhood.d.coefficient n +
      cauchyTwo BuiNeighborhood.x.coefficient BuiNeighborhood.r.coefficient n +
      cauchyTwo BuiNeighborhood.v.coefficient BuiNeighborhood.y.coefficient n +
      cauchyThree BuiNeighborhood.u.coefficient BuiNeighborhood.y.coefficient
        BuiNeighborhood.z.coefficient n := by
  rw [cauchyTwo_coefficient_eq_buiPairAggregateCount,
    cauchyTwo_coefficient_eq_buiPairAggregateCount,
    cauchyTwo_coefficient_eq_buiPairAggregateCount,
    cauchyTwo_coefficient_eq_buiPairAggregateCount,
    cauchyThree_coefficient_eq_buiTripleAggregateCount]
  unfold BuiNeighborhood.coefficient
  exact_mod_cast buiP_aggregateOccurrenceCount_le n

/-- The `p` field required by `GeometricBuiGaps`, discharged directly from
finite polyomino geometry. -/
theorem geometricCoefficientProfile_p_recurrence (n : ℕ) (_hn : 2 ≤ n) :
    geometricCoefficientProfile.p n ≤
      cauchyTwo geometricCoefficientProfile.e geometricCoefficientProfile.h n +
      cauchyTwo geometricCoefficientProfile.q geometricCoefficientProfile.d n +
      cauchyTwo geometricCoefficientProfile.x geometricCoefficientProfile.r n +
      cauchyTwo geometricCoefficientProfile.v geometricCoefficientProfile.y n +
      cauchyThree geometricCoefficientProfile.u geometricCoefficientProfile.y
        geometricCoefficientProfile.z n := by
  simpa [geometricCoefficientProfile] using buiP_coefficient_le n


end LeanProofs.KlarnerConstant
