import KlarnerConstant.GeometricProfile
import KlarnerConstant.SeededPartition

/-!
# Core infrastructure for the five-branch geometric recurrence

This module contains the lattice symmetries, lossless marked-piece encoding,
and finite-cardinality bridge shared by the geometric construction and its
final injection proof.
-/

namespace LeanProofs.KlarnerConstant

namespace GeometricFourFiveInternal

def cellAt (anchor : Cell) (dx dy : ℤ) : Cell :=
  anchor + (dx, dy)

theorem cellAt_zero (anchor : Cell) : cellAt anchor 0 0 = anchor := by
  apply Prod.ext <;> dsimp [cellAt] <;> omega

@[simp]
theorem cellAt_add_offset (anchor : Cell) (dx dy ex ey : ℤ) :
    cellAt anchor dx dy + (ex, ey) =
      cellAt anchor (dx + ex) (dy + ey) := by
  apply Prod.ext <;> dsimp [cellAt] <;> omega

@[simp]
theorem cellAt_eq_cellAt_iff (anchor : Cell) (dx dy ex ey : ℤ) :
    cellAt anchor dx dy = cellAt anchor ex ey ↔ dx = ex ∧ dy = ey := by
  constructor
  · intro h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    dsimp [cellAt] at hx hy
    exact ⟨by omega, by omega⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ## The three grid symmetries used by the branch maps -/

structure GridSymmetry where
  equiv : Cell ≃+ Cell
  adjacent_iff : ∀ a b, EdgeAdjacent (equiv a) (equiv b) ↔ EdgeAdjacent a b

def diagonalEquiv : Cell ≃+ Cell where
  toFun c := (c.2, c.1)
  invFun c := (c.2, c.1)
  left_inv c := by cases c; rfl
  right_inv c := by cases c; rfl
  map_add' a b := by apply Prod.ext <;> dsimp <;> omega

def verticalEquiv : Cell ≃+ Cell where
  toFun c := (-c.1, c.2)
  invFun c := (-c.1, c.2)
  left_inv c := by apply Prod.ext <;> dsimp <;> omega
  right_inv c := by apply Prod.ext <;> dsimp <;> omega
  map_add' a b := by apply Prod.ext <;> dsimp <;> omega

def quarterTurnEquiv : Cell ≃+ Cell where
  toFun c := (-c.2, c.1)
  invFun c := (c.2, -c.1)
  left_inv c := by apply Prod.ext <;> dsimp <;> omega
  right_inv c := by apply Prod.ext <;> dsimp <;> omega
  map_add' a b := by apply Prod.ext <;> dsimp <;> omega

def identitySymmetry : GridSymmetry where
  equiv := AddEquiv.refl Cell
  adjacent_iff a b := Iff.rfl

@[simp]
theorem identitySymmetry_apply (c : Cell) :
    identitySymmetry.equiv c = c := by
  rfl

def diagonalSymmetry : GridSymmetry where
  equiv := diagonalEquiv
  adjacent_iff a b := by
    rcases a with ⟨ax, ay⟩
    rcases b with ⟨bx, byy⟩
    simp [EdgeAdjacent, diagonalEquiv]
    omega

def verticalSymmetry : GridSymmetry where
  equiv := verticalEquiv
  adjacent_iff a b := by
    rcases a with ⟨ax, ay⟩
    rcases b with ⟨bx, byy⟩
    simp [EdgeAdjacent, verticalEquiv]
    omega

def quarterTurnSymmetry : GridSymmetry where
  equiv := quarterTurnEquiv
  adjacent_iff a b := by
    rcases a with ⟨ax, ay⟩
    rcases b with ⟨bx, byy⟩
    simp [EdgeAdjacent, quarterTurnEquiv]
    omega

namespace GridSymmetry

def transformCells (sigma : GridSymmetry) (cells : Finset Cell) :
    Finset Cell :=
  cells.image sigma.equiv

@[simp]
theorem mem_transformCells (sigma : GridSymmetry)
    {cells : Finset Cell} {c : Cell} :
    sigma.equiv c ∈ sigma.transformCells cells ↔ c ∈ cells := by
  simp [transformCells]

def transformPolyomino (sigma : GridSymmetry) (P : Polyomino) :
    Polyomino where
  cells := sigma.transformCells P.cells
  nonempty := P.nonempty.image sigma.equiv
  edgeConnected := by
    intro a ha b hb
    rcases Finset.mem_image.mp ha with ⟨a0, ha0, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨b0, hb0, rfl⟩
    apply Relation.ReflTransGen.lift sigma.equiv
    · intro x y (hxy : EdgeAdjacentIn P.cells x y)
      exact ⟨Finset.mem_image.mpr ⟨x, hxy.1, rfl⟩,
        Finset.mem_image.mpr ⟨y, hxy.2.1, rfl⟩,
        (sigma.adjacent_iff x y).2 hxy.2.2⟩
    · exact P.edgeConnected a0 ha0 b0 hb0

@[simp]
theorem identity_transformPolyomino_cells (P : Polyomino) :
    (identitySymmetry.transformPolyomino P).cells = P.cells := by
  ext c
  simp [transformPolyomino, transformCells, identitySymmetry]

@[simp]
theorem card_transformPolyomino (sigma : GridSymmetry) (P : Polyomino) :
    (sigma.transformPolyomino P).cells.card = P.cells.card := by
  exact Finset.card_image_of_injective P.cells sigma.equiv.injective

end GridSymmetry

/-! ## Marked normalized pieces and their lossless decoder -/

theorem mem_occurrenceAnchors_iff (pattern : OffsetPattern)
    (cells : Finset Cell) (anchor : Cell) :
    anchor ∈ pattern.occurrenceAnchors cells ↔
      anchor ∈ cells ∧ pattern.OccursAt cells anchor := by
  classical
  simp [OffsetPattern.occurrenceAnchors]

noncomputable def makeMarkedPiece (kind : BuiNeighborhood)
    (sigma : GridSymmetry) (P : Polyomino) (rawAnchor : Cell)
    (hanchor : rawAnchor ∈ P.cells)
    (hpattern : kind.pattern.OccursAt
      (sigma.transformPolyomino P).cells (sigma.equiv rawAnchor)) :
    MarkedOccurrence kind P.cells.card := by
  classical
  let Q := sigma.transformPolyomino P
  let shift := -Q.southwestAnchor
  let N : NormalizedPolyomino P.cells.card := {
    toPolyomino := Q.normalize
    southwestAnchor_eq := Q.southwestAnchor_normalize
    card_cells := by
      change (Q.cells.image
        (fun c ↦ -Q.southwestAnchor + c)).card = P.cells.card
      calc
        (Q.cells.image (fun c ↦ -Q.southwestAnchor + c)).card =
            Q.cells.card :=
          Finset.card_image_of_injective Q.cells
            (add_right_injective (-Q.southwestAnchor))
        _ = P.cells.card := GridSymmetry.card_transformPolyomino sigma P }
  refine ⟨N, ⟨shift + sigma.equiv rawAnchor, ?_⟩⟩
  apply (mem_occurrenceAnchors_iff _ _ _).2
  refine ⟨?_, hpattern.translate shift⟩
  change shift + sigma.equiv rawAnchor ∈
    Q.cells.image (fun c => shift + c)
  exact Finset.mem_image.mpr ⟨sigma.equiv rawAnchor,
    Finset.mem_image.mpr ⟨rawAnchor, hanchor, rfl⟩, rfl⟩

/-- Decode a normalized marked factor into source coordinates, putting its
raw marked cell at the supplied offset from the source occurrence anchor. -/
def recoverPiece {kind : BuiNeighborhood} {n : ℕ}
    (sigma : GridSymmetry) (rawAnchorOffset : Cell)
    (out : MarkedOccurrence kind n) : Finset Cell :=
  out.1.toPolyomino.cells.image fun c =>
    rawAnchorOffset + sigma.equiv.symm (c - out.2.1)

theorem recover_makeMarkedPiece (kind : BuiNeighborhood)
    (sigma : GridSymmetry) (P : Polyomino) (sourceAnchor rawAnchor offset : Cell)
    (hraw : rawAnchor = sourceAnchor + offset)
    (hanchor : rawAnchor ∈ P.cells)
    (hpattern : kind.pattern.OccursAt
      (sigma.transformPolyomino P).cells (sigma.equiv rawAnchor)) :
    recoverPiece sigma offset
        (makeMarkedPiece kind sigma P rawAnchor hanchor hpattern) =
      P.cells.image (fun c => -sourceAnchor + c) := by
  classical
  simp only [recoverPiece, makeMarkedPiece,
    Polyomino.normalize, Polyomino.cells_translate,
    GridSymmetry.transformPolyomino, GridSymmetry.transformCells,
    Finset.image_image, Function.comp_apply]
  apply Finset.image_congr
  intro c hc
  change offset + sigma.equiv.symm
      ((-((sigma.transformPolyomino P).southwestAnchor) + sigma.equiv c) -
        (-((sigma.transformPolyomino P).southwestAnchor) +
          sigma.equiv rawAnchor)) =
    -sourceAnchor + c
  have hcancel :
      (-((sigma.transformPolyomino P).southwestAnchor) + sigma.equiv c) -
          (-((sigma.transformPolyomino P).southwestAnchor) +
            sigma.equiv rawAnchor) =
        sigma.equiv c - sigma.equiv rawAnchor := by
    abel
  rw [hcancel, ← sigma.equiv.map_sub, sigma.equiv.symm_apply_apply, hraw]
  abel

/-- Package a marked piece at a propositionally equal prescribed cardinality.
Keeping the transport inside this constructor gives the decoder a stable term
to rewrite, instead of exposing an opaque `Eq.rec` in each branch map. -/
noncomputable def makeMarkedPieceOfCard (kind : BuiNeighborhood)
    (sigma : GridSymmetry) (P : Polyomino) (rawAnchor : Cell)
    (hanchor : rawAnchor ∈ P.cells)
    (hpattern : kind.pattern.OccursAt
      (sigma.transformPolyomino P).cells (sigma.equiv rawAnchor))
    {n : ℕ} (hcard : P.cells.card = n) : MarkedOccurrence kind n :=
  hcard ▸ makeMarkedPiece kind sigma P rawAnchor hanchor hpattern

theorem recover_makeMarkedPieceOfCard (kind : BuiNeighborhood)
    (sigma : GridSymmetry) (P : Polyomino) (sourceAnchor rawAnchor offset : Cell)
    (hraw : rawAnchor = sourceAnchor + offset)
    (hanchor : rawAnchor ∈ P.cells)
    (hpattern : kind.pattern.OccursAt
      (sigma.transformPolyomino P).cells (sigma.equiv rawAnchor))
    {n : ℕ} (hcard : P.cells.card = n) :
    recoverPiece sigma offset
        (makeMarkedPieceOfCard kind sigma P rawAnchor hanchor hpattern hcard) =
      P.cells.image (fun c => -sourceAnchor + c) := by
  subst n
  simpa [makeMarkedPieceOfCard] using
    recover_makeMarkedPiece kind sigma P sourceAnchor rawAnchor offset
      hraw hanchor hpattern

def anchoredCells {kind : BuiNeighborhood} {n : ℕ}
    (x : MarkedOccurrence kind n) : Finset Cell :=
  x.1.toPolyomino.cells.image fun c => -x.2.1 + c

theorem anchoredCells_injective (kind : BuiNeighborhood) (n : ℕ) :
    Function.Injective (anchoredCells : MarkedOccurrence kind n → Finset Cell) := by
  intro x y hxy
  let PX := x.1.toPolyomino.translate (-x.2.1)
  let PY := y.1.toPolyomino.translate (-y.2.1)
  have hpoly : PX = PY := by
    apply Polyomino.ext
    exact hxy
  have hmarks : x.2.1 = y.2.1 := by
    have hsw := congrArg Polyomino.southwestAnchor hpoly
    dsimp only [PX, PY] at hsw
    rw [Polyomino.southwestAnchor_translate,
      Polyomino.southwestAnchor_translate] at hsw
    rw [x.1.southwestAnchor_eq, y.1.southwestAnchor_eq] at hsw
    have hneg : -x.2.1 = -y.2.1 := by simpa using hsw
    exact neg_injective hneg
  have hnormalized := congrArg Polyomino.normalize hpoly
  dsimp only [PX, PY] at hnormalized
  rw [Polyomino.normalize_translate, Polyomino.normalize_translate,
    x.1.normalize_toPolyomino, y.1.normalize_toPolyomino] at hnormalized
  have hP : x.1 = y.1 := NormalizedPolyomino.ext hnormalized
  cases x with
  | mk P a =>
      cases y with
      | mk Q b =>
          dsimp at hP hmarks
          cases hP
          have : a = b := Subtype.ext hmarks
          cases this
          rfl

/-! ## Finite convolution targets -/

abbrev AntidiagonalIndex (m : ℕ) :=
  {ij : ℕ × ℕ //
    ij ∈ Finset.Nat.instHasAntidiagonal.antidiagonal m}

abbrev MarkedPair (left right : BuiNeighborhood) (m : ℕ) :=
  Σ ij : AntidiagonalIndex m,
    MarkedOccurrence left ij.1.1 × MarkedOccurrence right ij.1.2

theorem aggregate_zero (kind : BuiNeighborhood) :
    kind.aggregateOccurrenceCount 0 = 0 := by
  classical
  unfold BuiNeighborhood.aggregateOccurrenceCount
  apply Finset.sum_eq_zero
  intro P _
  have hpos : 0 < P.toPolyomino.cells.card :=
    Finset.card_pos.mpr P.toPolyomino.nonempty
  rw [P.card_cells] at hpos
  omega

theorem card_markedOccurrence (kind : BuiNeighborhood) (n : ℕ) :
    Fintype.card (MarkedOccurrence kind n) =
      kind.aggregateOccurrenceCount n := by
  classical
  change Fintype.card
      (Σ P : NormalizedPolyomino n,
        {anchor : Cell //
          anchor ∈ kind.pattern.occurrenceAnchors P.toPolyomino.cells}) = _
  unfold BuiNeighborhood.aggregateOccurrenceCount
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro P _
  change Fintype.card
      {anchor : Cell //
        anchor ∈ kind.pattern.occurrenceAnchors P.toPolyomino.cells} =
    kind.occurrenceCount P.toPolyomino
  change Fintype.card
      {anchor : Cell //
        anchor ∈ kind.pattern.occurrenceAnchors P.toPolyomino.cells} =
    (kind.pattern.occurrenceAnchors P.toPolyomino.cells).card
  exact Fintype.card_coe _

noncomputable def positiveAggregate (kind : BuiNeighborhood) : ℕ → ℕ
  | 0 => 0
  | n + 1 => kind.aggregateOccurrenceCount (n + 1)

theorem card_markedOccurrence_eq_positiveAggregate
    (kind : BuiNeighborhood) (n : ℕ) :
    Fintype.card (MarkedOccurrence kind n) = positiveAggregate kind n := by
  cases n with
  | zero =>
      rw [card_markedOccurrence, aggregate_zero]
      rfl
  | succ n =>
      rw [card_markedOccurrence]
      rfl

noncomputable def aggregateConvolution
    (left right : BuiNeighborhood) (m : ℕ) : ℕ :=
  ∑ ij ∈ Finset.Nat.instHasAntidiagonal.antidiagonal m,
    positiveAggregate left ij.1 * positiveAggregate right ij.2

theorem card_markedPair (left right : BuiNeighborhood) (m : ℕ) :
    Fintype.card (MarkedPair left right m) =
      aggregateConvolution left right m := by
  classical
  change Fintype.card
      (Σ ij : AntidiagonalIndex m,
        MarkedOccurrence left ij.1.1 × MarkedOccurrence right ij.1.2) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod,
    card_markedOccurrence_eq_positiveAggregate]
  rw [Finset.univ_eq_attach
    (Finset.Nat.instHasAntidiagonal.antidiagonal m)]
  unfold aggregateConvolution
  exact Finset.sum_attach
    (Finset.Nat.instHasAntidiagonal.antidiagonal m)
    (fun ij => positiveAggregate left ij.1 * positiveAggregate right ij.2)

theorem cauchyTwo_coefficient_eq_aggregateConvolution
    (left right : BuiNeighborhood) (m : ℕ) :
    cauchyTwo left.coefficient right.coefficient m =
      (aggregateConvolution left right m : ℚ) := by
  classical
  unfold cauchyTwo aggregateConvolution BuiNeighborhood.coefficient
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [Nat.cast_mul]
  congr 1
  · cases ij.1 <;> simp [positivePart, positiveAggregate]
  · cases ij.2 <;> simp [positivePart, positiveAggregate]

end GeometricFourFiveInternal

end LeanProofs.KlarnerConstant
