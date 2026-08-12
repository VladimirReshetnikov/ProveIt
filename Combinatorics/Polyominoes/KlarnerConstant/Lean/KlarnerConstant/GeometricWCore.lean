import KlarnerConstant.GeometricProfile
import KlarnerConstant.SeededPartition
import KlarnerConstant.Concatenation

/-!
# Geometric W recurrence: combinatorial core

This module formalizes the `W` row of Appendix B in Bui's convolutional
polyomino argument. For every `n` it proves

```
W(n) <= S(n-1) + (E*G)(n-2) + (X*E)(n-2) + (Y*T)(n-2).
```

The proof partitions globally marked occurrences by local occupancy, maps each
branch injectively to a one-factor or convolution target, and supplies explicit
lossless reconstructors after normalization.
-/

namespace LeanProofs.KlarnerConstant

namespace GeometricWInternal

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
  apply congrArg₂ (fun a b : ℚ => a * b)
  · cases ij.1 <;> simp [positivePart, positiveAggregate]
  · cases ij.2 <;> simp [positivePart, positiveAggregate]

/-! A cardinality-transport wrapper for the two single-factor branches. -/

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

/-! ## The marked `W` frame and elementary grid facts -/

structure WFrame (cells : Finset Cell) (anchor : Cell) : Prop where
  a_mem : cellAt anchor 0 0 ∈ cells
  b_mem : cellAt anchor 1 0 ∈ cells
  r_mem : cellAt anchor 2 0 ∈ cells
  leftNorth_not_mem : cellAt anchor (-1) 1 ∉ cells
  left_not_mem : cellAt anchor (-1) 0 ∉ cells
  southwest_not_mem : cellAt anchor (-1) (-1) ∉ cells
  south_not_mem : cellAt anchor 0 (-1) ∉ cells
  southeast_not_mem : cellAt anchor 1 (-1) ∉ cells
  farSoutheast_not_mem : cellAt anchor 2 (-1) ∉ cells

def wA (anchor : Cell) := cellAt anchor 0 0
def wB (anchor : Cell) := cellAt anchor 1 0
def wU (anchor : Cell) := cellAt anchor 0 1
def wV (anchor : Cell) := cellAt anchor 1 1
def wR (anchor : Cell) := cellAt anchor 2 0
def wS (anchor : Cell) := cellAt anchor 2 1
def wTopV (anchor : Cell) := cellAt anchor 1 2
def wTopS (anchor : Cell) := cellAt anchor 2 2

@[simp]
theorem wA_add_offset (anchor : Cell) (dx dy : ℤ) :
    wA anchor + (dx, dy) = cellAt anchor dx dy := by
  simp [wA]

@[simp]
theorem wB_add_offset (anchor : Cell) (dx dy : ℤ) :
    wB anchor + (dx, dy) = cellAt anchor (1 + dx) dy := by
  simp [wB]

@[simp]
theorem wU_add_offset (anchor : Cell) (dx dy : ℤ) :
    wU anchor + (dx, dy) = cellAt anchor dx (1 + dy) := by
  simp [wU]

@[simp]
theorem wV_add_offset (anchor : Cell) (dx dy : ℤ) :
    wV anchor + (dx, dy) = cellAt anchor (1 + dx) (1 + dy) := by
  simp [wV]

@[simp]
theorem wR_add_offset (anchor : Cell) (dx dy : ℤ) :
    wR anchor + (dx, dy) = cellAt anchor (2 + dx) dy := by
  simp [wR]

@[simp]
theorem wS_add_offset (anchor : Cell) (dx dy : ℤ) :
    wS anchor + (dx, dy) = cellAt anchor (2 + dx) (1 + dy) := by
  simp [wS]

theorem wFrame_of_occursAt {cells : Finset Cell} {anchor : Cell}
    (h : buiWPattern.OccursAt cells anchor) : WFrame cells anchor := by
  constructor
  · exact h.1 (0, 0) (by simp [buiWPattern])
  · exact h.1 (1, 0) (by simp [buiWPattern])
  · exact h.1 (2, 0) (by simp [buiWPattern])
  · exact h.2 (-1, 1) (by simp [buiWPattern])
  · exact h.2 (-1, 0) (by simp [buiWPattern])
  · exact h.2 (-1, -1) (by simp [buiWPattern])
  · exact h.2 (0, -1) (by simp [buiWPattern])
  · exact h.2 (1, -1) (by simp [buiWPattern])
  · exact h.2 (2, -1) (by simp [buiWPattern])

theorem marked_occursAt {kind : BuiNeighborhood} {n : ℕ}
    (x : MarkedOccurrence kind n) :
    kind.pattern.OccursAt x.1.toPolyomino.cells x.2.1 := by
  exact ((mem_occurrenceAnchors_iff _ _ _).1 x.2.2).2

theorem wA_ne_wB (anchor : Cell) : wA anchor ≠ wB anchor := by
  intro h
  have := congrArg Prod.fst h
  simp [wA, wB, cellAt] at this <;> omega

theorem wA_ne_wU (anchor : Cell) : wA anchor ≠ wU anchor := by
  intro h
  have := congrArg Prod.snd h
  simp [wA, wU, cellAt] at this <;> omega

theorem wB_ne_wV (anchor : Cell) : wB anchor ≠ wV anchor := by
  intro h
  have := congrArg Prod.snd h
  simp [wB, wV, cellAt] at this <;> omega

theorem wA_ne_wV (anchor : Cell) : wA anchor ≠ wV anchor := by
  intro h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp [wA, wV, cellAt] at hx hy <;> omega

theorem wU_ne_wB (anchor : Cell) : wU anchor ≠ wB anchor := by
  intro h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp [wU, wB, cellAt] at hx hy <;> omega

theorem w_a_neighbors {cells : Finset Cell} {anchor c : Cell}
    (frame : WFrame cells anchor) (hc : c ∈ cells)
    (hadj : EdgeAdjacent (wA anchor) c) :
    c = wB anchor ∨ c = wU anchor := by
  rw [wA, cellAt_zero] at hadj
  rcases hadj with h | h | h | h
  · left; rw [h]; apply Prod.ext <;> dsimp [wB, cellAt] <;> omega
  · exfalso
    apply frame.left_not_mem
    have hc' := hc
    rw [h] at hc'
    convert hc' using 1 <;> apply Prod.ext <;> dsimp [cellAt, wA] <;> omega
  · right; rw [h]; apply Prod.ext <;> dsimp [wU, cellAt] <;> omega
  · exfalso
    apply frame.south_not_mem
    have hc' := hc
    rw [h] at hc'
    convert hc' using 1 <;> apply Prod.ext <;> dsimp [cellAt, wA] <;> omega

theorem w_b_neighbors_of_r_absent
    {cells : Finset Cell} {anchor c : Cell}
    (frame : WFrame cells anchor) (hr : wR anchor ∉ cells)
    (hc : c ∈ cells) (hadj : EdgeAdjacent (wB anchor) c) :
    c = wA anchor ∨ c = wV anchor := by
  rcases hadj with h | h | h | h
  · exfalso
    apply hr
    have hc' := hc
    rw [h] at hc'
    convert hc' using 1 <;> apply Prod.ext <;> dsimp [wB, wR, cellAt] <;> omega
  · left
    rw [h]
    apply Prod.ext <;> dsimp [wA, wB, cellAt] <;> omega
  · right
    rw [h]
    apply Prod.ext <;> dsimp [wV, wB, cellAt] <;> omega
  · exfalso
    apply frame.southeast_not_mem
    have hc' := hc
    rw [h] at hc'
    convert hc' using 1 <;> apply Prod.ext <;> dsimp [wB, cellAt] <;> omega

theorem w_lowerDomino_boundary {cells : Finset Cell}
    {anchor d c : Cell} (frame : WFrame cells anchor)
    (hd : d ∈ ({wA anchor, wB anchor} : Finset Cell))
    (hc : c ∈ cells) (hcDeleted : c ∉ ({wA anchor, wB anchor} : Finset Cell))
    (hadj : EdgeAdjacent d c) :
    c ∈ ({wU anchor, wV anchor, wR anchor} : Finset Cell) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl
  · rcases w_a_neighbors frame hc hadj with rfl | rfl
    · exact (hcDeleted (by simp)).elim
    · simp
  · rcases hadj with h | h | h | h
    · rw [h]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      right; right
      apply Prod.ext <;> dsimp [wB, wR, cellAt] <;> omega
    · have hca : c = wA anchor := by
        rw [h]
        apply Prod.ext <;> dsimp [wA, wB, cellAt] <;> omega
      exact (hcDeleted (by simp [hca])).elim
    · rw [h]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      right; left
      apply Prod.ext <;> dsimp [wV, wB, cellAt] <;> omega
    · exfalso
      apply frame.southeast_not_mem
      have hc' := hc
      rw [h] at hc'
      convert hc' using 1 <;> apply Prod.ext <;> dsimp [wB, cellAt] <;> omega

/-! ## Connectivity after deleting marked cells -/

theorem edgeAdjacentIn_symm {cells : Finset Cell} {a b : Cell}
    (h : EdgeAdjacentIn cells a b) : EdgeAdjacentIn cells b a :=
  ⟨h.2.1, h.1, edgeAdjacent_symm h.2.2⟩

theorem reflTransGen_symm {r : Cell → Cell → Prop}
    (hsymm : ∀ {a b}, r a b → r b a) {a b : Cell}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
      exact (Relation.ReflTransGen.single (hsymm hbc)).trans ih

/-- In a connected set, after deleting finitely many cells, every remaining
component meets a prescribed seed union as soon as every edge exiting the
deleted set lands in that union. -/
theorem reaches_seedUnion_after_delete (P : Polyomino)
    (deleted seedUnion : Finset Cell) (seed0 : Cell)
    (hseed0Cells : seed0 ∈ P.cells)
    (hseed0Deleted : seed0 ∉ deleted)
    (hseed0Seed : seed0 ∈ seedUnion)
    (hboundary : ∀ {d c : Cell}, d ∈ deleted → c ∈ P.cells →
      c ∉ deleted → EdgeAdjacent d c → c ∈ seedUnion)
    {c : Cell} (hc : c ∈ P.cells \ deleted) :
    ∃ s, s ∈ seedUnion ∧
      Relation.ReflTransGen (EdgeAdjacentIn (P.cells \ deleted)) c s := by
  have hpath := P.edgeConnected seed0 hseed0Cells c
    (Finset.mem_sdiff.mp hc).1
  have forward : ∀ {z : Cell},
      Relation.ReflTransGen (EdgeAdjacentIn P.cells) seed0 z →
      z ∉ deleted →
      ∃ s, s ∈ seedUnion ∧
        Relation.ReflTransGen (EdgeAdjacentIn (P.cells \ deleted)) s z := by
    intro z hz
    induction hz with
    | refl =>
        intro _
        exact ⟨seed0, hseed0Seed, Relation.ReflTransGen.refl⟩
    | @tail y z hyz hstep ih =>
        intro hzDeleted
        by_cases hyDeleted : y ∈ deleted
        · have hzSeed := hboundary hyDeleted hstep.2.1 hzDeleted hstep.2.2
          exact ⟨z, hzSeed, Relation.ReflTransGen.refl⟩
        · rcases ih hyDeleted with ⟨s, hs, hsy⟩
          refine ⟨s, hs, hsy.tail ?_⟩
          exact ⟨Finset.mem_sdiff.mpr ⟨hstep.1, hyDeleted⟩,
            Finset.mem_sdiff.mpr ⟨hstep.2.1, hzDeleted⟩, hstep.2.2⟩
  rcases forward hpath (Finset.mem_sdiff.mp hc).2 with ⟨s, hs, hsc⟩
  exact ⟨s, hs, reflTransGen_symm edgeAdjacentIn_symm hsc⟩

def deletionSeedSystem (P : Polyomino) (deleted : Finset Cell)
    (seeds : Bool → Finset Cell)
    (hsubset : ∀ i, seeds i ⊆ P.cells \ deleted)
    (hnonempty : ∀ i, (seeds i).Nonempty)
    (hconnected : ∀ i, EdgeConnected (seeds i))
    (hdisjoint : Disjoint (seeds false) (seeds true))
    (seed0 : Cell) (hseed0 : seed0 ∈ seeds false)
    (hboundary : ∀ {d c : Cell}, d ∈ deleted → c ∈ P.cells →
      c ∉ deleted → EdgeAdjacent d c →
        c ∈ allSeedCells seeds) : SeedSystem Bool where
  cells := P.cells \ deleted
  seeds := seeds
  seed_subset := hsubset
  seed_nonempty := hnonempty
  seed_connected := hconnected
  seed_pairwise_disjoint := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hdisjoint
    · exact hdisjoint.symm
    · exact (hij rfl).elim
  reaches_seed := by
    intro c hc
    have hseed0Ambient := hsubset false hseed0
    rcases reaches_seedUnion_after_delete P deleted (allSeedCells seeds) seed0
        (Finset.mem_sdiff.mp hseed0Ambient).1
        (Finset.mem_sdiff.mp hseed0Ambient).2
        (mem_coveredCells.mpr ⟨false, hseed0⟩) hboundary hc with
      ⟨s, hs, hcs⟩
    rcases mem_coveredCells.mp hs with ⟨i, hsi⟩
    exact ⟨i, s, hsi, hcs⟩

theorem edgeConnected_singleton (a : Cell) :
    EdgeConnected ({a} : Finset Cell) := by
  intro x hx y hy
  simp only [Finset.mem_singleton] at hx hy
  subst x
  subst y
  exact Relation.ReflTransGen.refl

theorem edgeConnected_pair {a b : Cell} (hab : EdgeAdjacent a b) :
    EdgeConnected ({a, b} : Finset Cell) := by
  intro x hx y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨by simp, by simp, hab⟩
  · exact Relation.ReflTransGen.single ⟨by simp, by simp, edgeAdjacent_symm hab⟩
  · exact Relation.ReflTransGen.refl

theorem edgeConnected_triple {a b c : Cell}
    (hab : EdgeAdjacent a b) (hbc : EdgeAdjacent b c) :
    EdgeConnected ({a, b, c} : Finset Cell) := by
  intro x hx y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨by simp, by simp, hab⟩
  · exact (Relation.ReflTransGen.single
      ⟨by simp, by simp, hab⟩).tail ⟨by simp, by simp, hbc⟩
  · exact Relation.ReflTransGen.single ⟨by simp, by simp,
      edgeAdjacent_symm hab⟩
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨by simp, by simp, hbc⟩
  · exact (Relation.ReflTransGen.single
      ⟨by simp, by simp, edgeAdjacent_symm hbc⟩).tail
        ⟨by simp, by simp, edgeAdjacent_symm hab⟩
  · exact Relation.ReflTransGen.single ⟨by simp, by simp,
      edgeAdjacent_symm hbc⟩
  · exact Relation.ReflTransGen.refl

def chainSeed (cells : Finset Cell) (a b c : Cell) : Finset Cell :=
  if c ∈ cells then {a, b, c} else {a, b}

theorem mem_chainSeed_iff {cells : Finset Cell} {a b c x : Cell} :
    x ∈ chainSeed cells a b c ↔
      x = a ∨ x = b ∨ (x = c ∧ c ∈ cells) := by
  by_cases hc : c ∈ cells <;> simp [chainSeed, hc]

theorem chainSeed_subset {cells : Finset Cell} {a b c : Cell}
    (ha : a ∈ cells) (hb : b ∈ cells) :
    chainSeed cells a b c ⊆ cells := by
  intro x hx
  by_cases hc : c ∈ cells
  · simp only [chainSeed, hc, if_true, Finset.mem_insert,
      Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · simp only [chainSeed, hc, if_false, Finset.mem_insert,
      Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption

theorem chainSeed_nonempty (cells : Finset Cell) (a b c : Cell) :
    (chainSeed cells a b c).Nonempty := by
  by_cases hc : c ∈ cells
  · exact ⟨a, by simp [chainSeed, hc]⟩
  · exact ⟨a, by simp [chainSeed, hc]⟩

theorem chainSeed_connected {cells : Finset Cell} {a b c : Cell}
    (hab : EdgeAdjacent a b) (hbc : EdgeAdjacent b c) :
    EdgeConnected (chainSeed cells a b c) := by
  by_cases hc : c ∈ cells
  · rw [chainSeed, if_pos hc]
    exact edgeConnected_triple hab hbc
  · rw [chainSeed, if_neg hc]
    exact edgeConnected_pair hab

theorem cellAt_east (anchor : Cell) (dx dy : ℤ) :
    EdgeAdjacent (cellAt anchor dx dy) (cellAt anchor (dx + 1) dy) := by
  left
  apply Prod.ext <;> dsimp [cellAt] <;> omega

theorem cellAt_north (anchor : Cell) (dx dy : ℤ) :
    EdgeAdjacent (cellAt anchor dx dy) (cellAt anchor dx (dy + 1)) := by
  right; right; left
  apply Prod.ext <;> dsimp [cellAt] <;> omega

end GeometricWInternal
end LeanProofs.KlarnerConstant

