import KlarnerConstant.GeometricDeletion

/-!
# The `X`, `Y`, and `Z` deletion recurrences

This module formalizes the three three-branch local partitions in Appendix B
of Bui's recurrence argument:

* `X(n) <= D(n - 1) + G(n - 2) + U(n - 2)`,
* `Y(n) <= C(n - 1) + G(n - 2) + T(n - 2)`, and
* `Z(n) <= C(n - 1) + E(n - 2) + X(n - 2)`.

In each source occurrence the two required cells form a horizontal lower
domino.  We split by occupancy of the two cells immediately above it.  The
first branch deletes one forced leaf.  The other branches delete the lower
domino; connectivity is preserved because either the right lower cell is a
leaf and then the left one is a leaf, or the two occupied upper cells provide
an alternate edge after both lower cells are removed.

There is one orientation issue hidden by the diagrams in the paper.  In the
middle `X` branch the surviving cell has the reflected `G` neighborhood: its
east cell, rather than its west cell, is absent.  We therefore reflect the
remainder horizontally and normalize it.  Horizontal reflection is developed
below as an explicit involutive injection, so no symmetry assumption is used.
-/

namespace LeanProofs.KlarnerConstant

private def cellAt (anchor : Cell) (dx dy : ℤ) : Cell :=
  anchor + (dx, dy)

private theorem cellAt_right_ne (anchor : Cell) :
    cellAt anchor 1 0 ≠ anchor := by
  intro h
  have h' := congrArg Prod.fst h
  simp [cellAt] at h'

private theorem cellAt_north_ne (anchor : Cell) :
    cellAt anchor 0 1 ≠ anchor := by
  intro h
  have h' := congrArg Prod.snd h
  simp [cellAt] at h'

private theorem cellAt_north_ne_right (anchor : Cell) :
    cellAt anchor 0 1 ≠ cellAt anchor 1 0 := by
  intro h
  have h' := congrArg Prod.fst h
  simp [cellAt] at h'

private theorem cellAt_northeast_ne_left (anchor : Cell) :
    cellAt anchor 1 1 ≠ anchor := by
  intro h
  have h' := congrArg Prod.snd h
  simp [cellAt] at h'

private theorem cellAt_northeast_ne_right (anchor : Cell) :
    cellAt anchor 1 1 ≠ cellAt anchor 1 0 := by
  intro h
  have h' := congrArg Prod.snd h
  simp [cellAt] at h'

private theorem east_edge (anchor : Cell) :
    EdgeAdjacent anchor (cellAt anchor 1 0) := by
  left
  apply Prod.ext <;> simp [cellAt]

/-! ## Generic one-cell deletion with a retained parent mark -/

structure LeafAt (cells : Finset Cell) (anchor parent : Cell) : Prop where
  anchor_mem : anchor ∈ cells
  parent_mem : parent ∈ cells
  anchor_ne_parent : anchor ≠ parent
  only_neighbor : ∀ {other : Cell},
    other ∈ cells → EdgeAdjacent anchor other → other = parent

private def retractLeaf (anchor parent other : Cell) : Cell :=
  if other = anchor then parent else other

private theorem edgeConnected_erase_leaf {P : Polyomino} {anchor parent : Cell}
    (hleaf : LeafAt P.cells anchor parent) :
    EdgeConnected (P.cells.erase anchor) := by
  intro x hx y hy
  have hx' := Finset.mem_erase.mp hx
  have hy' := Finset.mem_erase.mp hy
  have mapEdge : ∀ {u v : Cell}, EdgeAdjacentIn P.cells u v →
      Relation.ReflTransGen (EdgeAdjacentIn (P.cells.erase anchor))
        (retractLeaf anchor parent u) (retractLeaf anchor parent v) := by
    intro u v huv
    by_cases hu : u = anchor
    · subst u
      have hvparent := hleaf.only_neighbor huv.2.1 huv.2.2
      subst v
      simpa [retractLeaf, hleaf.anchor_ne_parent] using
        (Relation.ReflTransGen.refl :
          Relation.ReflTransGen (EdgeAdjacentIn (P.cells.erase anchor))
            parent parent)
    · by_cases hv : v = anchor
      · subst v
        have huparent := hleaf.only_neighbor huv.1
          (edgeAdjacent_symm huv.2.2)
        subst u
        simpa [retractLeaf, hleaf.anchor_ne_parent] using
          (Relation.ReflTransGen.refl :
            Relation.ReflTransGen (EdgeAdjacentIn (P.cells.erase anchor))
              parent parent)
      · apply Relation.ReflTransGen.single
        simpa [retractLeaf, hu, hv] using
          (show EdgeAdjacentIn (P.cells.erase anchor) u v from
            ⟨Finset.mem_erase.mpr ⟨hu, huv.1⟩,
              Finset.mem_erase.mpr ⟨hv, huv.2.1⟩, huv.2.2⟩)
  have hpath := P.edgeConnected x hx'.2 y hy'.2
  have hlift := hpath.lift' (retractLeaf anchor parent)
    (fun _ _ hstep => mapEdge hstep)
  change Relation.ReflTransGen (EdgeAdjacentIn (P.cells.erase anchor))
    (retractLeaf anchor parent x) (retractLeaf anchor parent y) at hlift
  have hxfix : retractLeaf anchor parent x = x := by
    simp only [retractLeaf, if_neg hx'.1]
  have hyfix : retractLeaf anchor parent y = y := by
    simp only [retractLeaf, if_neg hy'.1]
  rw [hxfix, hyfix] at hlift
  exact hlift

private def Polyomino.eraseLeaf (P : Polyomino) (anchor parent : Cell)
    (hleaf : LeafAt P.cells anchor parent) : Polyomino where
  cells := P.cells.erase anchor
  nonempty := ⟨parent, Finset.mem_erase.mpr
    ⟨hleaf.anchor_ne_parent.symm, hleaf.parent_mem⟩⟩
  edgeConnected := edgeConnected_erase_leaf hleaf

/-- A leaf deletion whose deleted cell is at a fixed offset from the retained
marked parent.  The offset makes reconstruction uniform. -/
structure LeafDeletionOccurrence (n : ℕ) (deletedOffset : Cell) where
  polyomino : NormalizedPolyomino n
  anchor : Cell
  parent : Cell
  anchor_eq : anchor = parent + deletedOffset
  leaf : LeafAt polyomino.toPolyomino.cells anchor parent

namespace LeafDeletionOccurrence

@[ext]
theorem ext {n : ℕ} {offset : Cell}
    {x y : LeafDeletionOccurrence n offset}
    (hpolyomino : x.polyomino = y.polyomino)
    (hparent : x.parent = y.parent) : x = y := by
  cases x
  cases y
  cases hpolyomino
  cases hparent
  simp_all

def erased {n : ℕ} {offset : Cell}
    (x : LeafDeletionOccurrence n offset) : Polyomino :=
  x.polyomino.toPolyomino.eraseLeaf x.anchor x.parent x.leaf

noncomputable def normalizationVector {n : ℕ} {offset : Cell}
    (x : LeafDeletionOccurrence n offset) : Cell :=
  -x.erased.southwestAnchor

noncomputable def normalizedRemainder {n : ℕ} {offset : Cell}
    (x : LeafDeletionOccurrence n offset) : NormalizedPolyomino (n - 1) where
  toPolyomino := x.erased.translate x.normalizationVector
  southwestAnchor_eq := by
    rw [Polyomino.southwestAnchor_translate]
    apply Prod.ext <;> simp [normalizationVector]
  card_cells := by
    rw [Polyomino.card_cells_translate]
    change (x.polyomino.toPolyomino.cells.erase x.anchor).card = n - 1
    rw [Finset.card_erase_of_mem x.leaf.anchor_mem,
      x.polyomino.card_cells]

noncomputable def deleteData {n : ℕ} {offset : Cell}
    (x : LeafDeletionOccurrence n offset) :
    NormalizedPolyomino (n - 1) × Cell :=
  (x.normalizedRemainder, x.normalizationVector + x.parent)

private def reconstructCells {m : ℕ} {offset : Cell}
    (out : NormalizedPolyomino m × Cell) : Finset Cell :=
  insert (out.2 + offset) out.1.toPolyomino.cells

private theorem insert_image_erase (cells : Finset Cell) {anchor : Cell}
    (hanchor : anchor ∈ cells) (v : Cell) :
    insert (v + anchor) ((cells.erase anchor).image fun cell => v + cell) =
      cells.image fun cell => v + cell := by
  ext cell
  constructor
  · intro hcell
    rcases Finset.mem_insert.mp hcell with hcell | hcell
    · subst cell
      exact Finset.mem_image.mpr ⟨anchor, hanchor, rfl⟩
    · rcases Finset.mem_image.mp hcell with ⟨other, hother, rfl⟩
      exact Finset.mem_image.mpr
        ⟨other, (Finset.mem_erase.mp hother).2, rfl⟩
  · intro hcell
    rcases Finset.mem_image.mp hcell with ⟨other, hother, rfl⟩
    by_cases hEq : other = anchor
    · subst other
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem <|
        Finset.mem_image.mpr
          ⟨other, Finset.mem_erase.mpr ⟨hEq, hother⟩, rfl⟩

private theorem reconstruct_deleteData {n : ℕ} {offset : Cell}
    (x : LeafDeletionOccurrence n offset) :
    reconstructCells (offset := offset) x.deleteData =
      (x.polyomino.toPolyomino.translate x.normalizationVector).cells := by
  change insert
      ((x.normalizationVector + x.parent) + offset)
      ((x.polyomino.toPolyomino.cells.erase x.anchor).image
        fun cell => x.normalizationVector + cell) =
    x.polyomino.toPolyomino.cells.image
      (fun cell => x.normalizationVector + cell)
  have hdeleted : (x.normalizationVector + x.parent) + offset =
      x.normalizationVector + x.anchor := by
    calc
      (x.normalizationVector + x.parent) + offset =
          x.normalizationVector + (x.parent + offset) := add_assoc _ _ _
      _ = x.normalizationVector + x.anchor :=
        congrArg (fun cell : Cell => x.normalizationVector + cell)
          x.anchor_eq.symm
  rw [hdeleted]
  exact insert_image_erase _ x.leaf.anchor_mem _

theorem deleteData_injective (n : ℕ) (offset : Cell) :
    Function.Injective (deleteData : LeafDeletionOccurrence n offset →
      NormalizedPolyomino (n - 1) × Cell) := by
  intro x y hdelete
  have hreconstruct := congrArg (reconstructCells (offset := offset)) hdelete
  rw [reconstruct_deleteData, reconstruct_deleteData] at hreconstruct
  have htranslated :
      x.polyomino.toPolyomino.translate x.normalizationVector =
        y.polyomino.toPolyomino.translate y.normalizationVector :=
    Polyomino.ext hreconstruct
  have hvectors : x.normalizationVector = y.normalizationVector := by
    have hanchors := congrArg Polyomino.southwestAnchor htranslated
    rw [Polyomino.southwestAnchor_translate,
      Polyomino.southwestAnchor_translate,
      x.polyomino.southwestAnchor_eq,
      y.polyomino.southwestAnchor_eq] at hanchors
    simpa using hanchors
  have hnormalized := congrArg Polyomino.normalize htranslated
  rw [Polyomino.normalize_translate, Polyomino.normalize_translate,
    x.polyomino.normalize_toPolyomino,
    y.polyomino.normalize_toPolyomino] at hnormalized
  have hpolyomino : x.polyomino = y.polyomino :=
    NormalizedPolyomino.ext hnormalized
  have hmarks := congrArg Prod.snd hdelete
  change x.normalizationVector + x.parent =
    y.normalizationVector + y.parent at hmarks
  rw [hvectors] at hmarks
  have hparent : x.parent = y.parent := add_left_cancel hmarks
  exact LeafDeletionOccurrence.ext hpolyomino hparent

end LeafDeletionOccurrence

/-! ## Generic two-cell deletion with a retained mark -/

/-- A normalized occurrence in which two cells at fixed offsets from `mark`
can be deleted while leaving a connected, nonempty remainder. -/
structure PairDeletionOccurrence (n : ℕ) (firstOffset secondOffset : Cell) where
  polyomino : NormalizedPolyomino n
  mark : Cell
  mark_mem : mark ∈ polyomino.toPolyomino.cells
  first_mem : mark + firstOffset ∈ polyomino.toPolyomino.cells
  second_mem : mark + secondOffset ∈ polyomino.toPolyomino.cells
  first_ne_second : mark + firstOffset ≠ mark + secondOffset
  mark_ne_first : mark ≠ mark + firstOffset
  mark_ne_second : mark ≠ mark + secondOffset
  connected : EdgeConnected
    ((polyomino.toPolyomino.cells.erase (mark + firstOffset)).erase
      (mark + secondOffset))

namespace PairDeletionOccurrence

@[ext]
theorem ext {n : ℕ} {firstOffset secondOffset : Cell}
    {x y : PairDeletionOccurrence n firstOffset secondOffset}
    (hpolyomino : x.polyomino = y.polyomino)
    (hmark : x.mark = y.mark) : x = y := by
  cases x
  cases y
  cases hpolyomino
  cases hmark
  rfl

def erased {n : ℕ} {firstOffset secondOffset : Cell}
    (x : PairDeletionOccurrence n firstOffset secondOffset) : Polyomino where
  cells := (x.polyomino.toPolyomino.cells.erase (x.mark + firstOffset)).erase
    (x.mark + secondOffset)
  nonempty := by
    refine ⟨x.mark, Finset.mem_erase.mpr ⟨x.mark_ne_second, ?_⟩⟩
    exact Finset.mem_erase.mpr ⟨x.mark_ne_first, x.mark_mem⟩
  edgeConnected := x.connected

noncomputable def normalizationVector {n : ℕ}
    {firstOffset secondOffset : Cell}
    (x : PairDeletionOccurrence n firstOffset secondOffset) : Cell :=
  -x.erased.southwestAnchor

noncomputable def normalizedRemainder {n : ℕ}
    {firstOffset secondOffset : Cell}
    (x : PairDeletionOccurrence n firstOffset secondOffset) :
    NormalizedPolyomino (n - 2) where
  toPolyomino := x.erased.translate x.normalizationVector
  southwestAnchor_eq := by
    rw [Polyomino.southwestAnchor_translate]
    apply Prod.ext <;> simp [normalizationVector]
  card_cells := by
    rw [Polyomino.card_cells_translate]
    change ((x.polyomino.toPolyomino.cells.erase
      (x.mark + firstOffset)).erase (x.mark + secondOffset)).card = n - 2
    have hsecond : x.mark + secondOffset ∈
        x.polyomino.toPolyomino.cells.erase (x.mark + firstOffset) :=
      Finset.mem_erase.mpr ⟨x.first_ne_second.symm, x.second_mem⟩
    rw [Finset.card_erase_of_mem hsecond,
      Finset.card_erase_of_mem x.first_mem, x.polyomino.card_cells]
    omega

noncomputable def deleteData {n : ℕ} {firstOffset secondOffset : Cell}
    (x : PairDeletionOccurrence n firstOffset secondOffset) :
    NormalizedPolyomino (n - 2) × Cell :=
  (x.normalizedRemainder, x.normalizationVector + x.mark)

private def reconstructCells {m : ℕ} (firstOffset secondOffset : Cell)
    (out : NormalizedPolyomino m × Cell) : Finset Cell :=
  insert (out.2 + firstOffset)
    (insert (out.2 + secondOffset) out.1.toPolyomino.cells)

private theorem insert_image_erase (cells : Finset Cell) {anchor : Cell}
    (hanchor : anchor ∈ cells) (v : Cell) :
    insert (v + anchor) ((cells.erase anchor).image fun cell => v + cell) =
      cells.image fun cell => v + cell := by
  ext cell
  constructor
  · intro hcell
    rcases Finset.mem_insert.mp hcell with hcell | hcell
    · subst cell
      exact Finset.mem_image.mpr ⟨anchor, hanchor, rfl⟩
    · rcases Finset.mem_image.mp hcell with ⟨other, hother, rfl⟩
      exact Finset.mem_image.mpr
        ⟨other, (Finset.mem_erase.mp hother).2, rfl⟩
  · intro hcell
    rcases Finset.mem_image.mp hcell with ⟨other, hother, rfl⟩
    by_cases hEq : other = anchor
    · subst other
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem <|
        Finset.mem_image.mpr
          ⟨other, Finset.mem_erase.mpr ⟨hEq, hother⟩, rfl⟩

private theorem reconstruct_deleteData {n : ℕ}
    {firstOffset secondOffset : Cell}
    (x : PairDeletionOccurrence n firstOffset secondOffset) :
    reconstructCells firstOffset secondOffset x.deleteData =
      (x.polyomino.toPolyomino.translate x.normalizationVector).cells := by
  change insert
      ((x.normalizationVector + x.mark) + firstOffset)
      (insert ((x.normalizationVector + x.mark) + secondOffset)
        (((x.polyomino.toPolyomino.cells.erase
            (x.mark + firstOffset)).erase (x.mark + secondOffset)).image
          fun cell => x.normalizationVector + cell)) =
    x.polyomino.toPolyomino.cells.image
      (fun cell => x.normalizationVector + cell)
  rw [show (x.normalizationVector + x.mark) + firstOffset =
      x.normalizationVector + (x.mark + firstOffset) by simp [add_assoc]]
  rw [show (x.normalizationVector + x.mark) + secondOffset =
      x.normalizationVector + (x.mark + secondOffset) by simp [add_assoc]]
  have hsecond : x.mark + secondOffset ∈
      x.polyomino.toPolyomino.cells.erase (x.mark + firstOffset) :=
    Finset.mem_erase.mpr ⟨x.first_ne_second.symm, x.second_mem⟩
  rw [insert_image_erase _ hsecond]
  exact insert_image_erase _ x.first_mem _

theorem deleteData_injective (n : ℕ) (firstOffset secondOffset : Cell) :
    Function.Injective (deleteData :
      PairDeletionOccurrence n firstOffset secondOffset →
        NormalizedPolyomino (n - 2) × Cell) := by
  intro x y hdelete
  have hreconstruct :=
    congrArg (reconstructCells firstOffset secondOffset) hdelete
  rw [reconstruct_deleteData, reconstruct_deleteData] at hreconstruct
  have htranslated :
      x.polyomino.toPolyomino.translate x.normalizationVector =
        y.polyomino.toPolyomino.translate y.normalizationVector :=
    Polyomino.ext hreconstruct
  have hvectors : x.normalizationVector = y.normalizationVector := by
    have hanchors := congrArg Polyomino.southwestAnchor htranslated
    rw [Polyomino.southwestAnchor_translate,
      Polyomino.southwestAnchor_translate,
      x.polyomino.southwestAnchor_eq,
      y.polyomino.southwestAnchor_eq] at hanchors
    simpa using hanchors
  have hnormalized := congrArg Polyomino.normalize htranslated
  rw [Polyomino.normalize_translate, Polyomino.normalize_translate,
    x.polyomino.normalize_toPolyomino,
    y.polyomino.normalize_toPolyomino] at hnormalized
  have hpolyomino : x.polyomino = y.polyomino :=
    NormalizedPolyomino.ext hnormalized
  have hmarks := congrArg Prod.snd hdelete
  change x.normalizationVector + x.mark =
    y.normalizationVector + y.mark at hmarks
  rw [hvectors] at hmarks
  have hmark : x.mark = y.mark := add_left_cancel hmarks
  exact PairDeletionOccurrence.ext hpolyomino hmark

end PairDeletionOccurrence

/-! ## Uniform constructors for marked target occurrences -/

private theorem marked_occursAt {kind : BuiNeighborhood} {n : ℕ}
    (x : MarkedOccurrence kind n) :
    kind.pattern.OccursAt x.1.toPolyomino.cells x.2.1 := by
  classical
  have hx := x.2.2
  change x.2.1 ∈ x.1.toPolyomino.cells.filter
    (fun anchor => kind.pattern.OccursAt x.1.toPolyomino.cells anchor) at hx
  exact (Finset.mem_filter.mp hx).2

private theorem markedOccurrence_ext {kind : BuiNeighborhood} {n : ℕ}
    {x y : MarkedOccurrence kind n}
    (hpolyomino : x.1 = y.1) (hanchor : x.2.1 = y.2.1) : x = y := by
  cases x with
  | mk P anchor =>
      cases y with
      | mk Q other =>
          dsimp at hpolyomino hanchor
          cases hpolyomino
          have hsubtype : anchor = other := Subtype.ext hanchor
          cases hsubtype
          rfl

private theorem card_markedOccurrence (kind : BuiNeighborhood) (n : ℕ) :
    Fintype.card (MarkedOccurrence kind n) =
      kind.aggregateOccurrenceCount n := by
  classical
  simp [MarkedOccurrence, BuiNeighborhood.aggregateOccurrenceCount,
    BuiNeighborhood.occurrenceCount, OffsetPattern.occurrenceCount]

private noncomputable def markedAfterLeaf {α : Type}
    {target : BuiNeighborhood} {n : ℕ} {offset : Cell}
    (pack : α → LeafDeletionOccurrence n offset)
    (rawTarget : ∀ x, target.pattern.OccursAt (pack x).erased.cells
      (pack x).parent) :
    α → MarkedOccurrence target (n - 1) := fun x => by
  classical
  let leaf := pack x
  let out := leaf.deleteData
  refine ⟨out.1, ⟨out.2, ?_⟩⟩
  rw [OffsetPattern.occurrenceAnchors, Finset.mem_filter]
  have hparentErase : leaf.parent ∈ leaf.erased.cells := by
    exact Finset.mem_erase.mpr
      ⟨leaf.leaf.anchor_ne_parent.symm, leaf.leaf.parent_mem⟩
  constructor
  · change leaf.normalizationVector + leaf.parent ∈
      leaf.erased.cells.image (fun cell => leaf.normalizationVector + cell)
    exact Finset.mem_image.mpr ⟨leaf.parent, hparentErase, rfl⟩
  · change target.pattern.OccursAt
      (leaf.erased.cells.image (fun cell => leaf.normalizationVector + cell))
      (leaf.normalizationVector + leaf.parent)
    exact (rawTarget x).translate leaf.normalizationVector

private theorem markedAfterLeaf_injective {α : Type}
    {target : BuiNeighborhood} {n : ℕ} {offset : Cell}
    (pack : α → LeafDeletionOccurrence n offset)
    (hpack : Function.Injective pack)
    (rawTarget : ∀ x, target.pattern.OccursAt (pack x).erased.cells
      (pack x).parent) :
    Function.Injective (markedAfterLeaf pack rawTarget) := by
  intro x y hxy
  have hdata := congrArg
    (fun z : MarkedOccurrence target (n - 1) => (z.1, z.2.1)) hxy
  change (pack x).deleteData = (pack y).deleteData at hdata
  exact hpack (LeafDeletionOccurrence.deleteData_injective n offset hdata)

private noncomputable def markedAfterPair {α : Type}
    {target : BuiNeighborhood} {n : ℕ} {firstOffset secondOffset : Cell}
    (pack : α →
      PairDeletionOccurrence n firstOffset secondOffset)
    (rawTarget : ∀ x, target.pattern.OccursAt (pack x).erased.cells
      (pack x).mark) :
    α → MarkedOccurrence target (n - 2) := fun x => by
  classical
  let pair := pack x
  let out := pair.deleteData
  refine ⟨out.1, ⟨out.2, ?_⟩⟩
  rw [OffsetPattern.occurrenceAnchors, Finset.mem_filter]
  have hmarkErase : pair.mark ∈ pair.erased.cells := by
    exact Finset.mem_erase.mpr ⟨pair.mark_ne_second,
      Finset.mem_erase.mpr ⟨pair.mark_ne_first, pair.mark_mem⟩⟩
  constructor
  · change pair.normalizationVector + pair.mark ∈
      pair.erased.cells.image (fun cell => pair.normalizationVector + cell)
    exact Finset.mem_image.mpr ⟨pair.mark, hmarkErase, rfl⟩
  · change target.pattern.OccursAt
      (pair.erased.cells.image (fun cell => pair.normalizationVector + cell))
      (pair.normalizationVector + pair.mark)
    exact (rawTarget x).translate pair.normalizationVector

private theorem markedAfterPair_injective {α : Type}
    {target : BuiNeighborhood} {n : ℕ} {firstOffset secondOffset : Cell}
    (pack : α →
      PairDeletionOccurrence n firstOffset secondOffset)
    (hpack : Function.Injective pack)
    (rawTarget : ∀ x, target.pattern.OccursAt (pack x).erased.cells
      (pack x).mark) :
    Function.Injective (markedAfterPair pack rawTarget) := by
  intro x y hxy
  have hdata := congrArg
    (fun z : MarkedOccurrence target (n - 2) => (z.1, z.2.1)) hxy
  change (pack x).deleteData = (pack y).deleteData at hdata
  exact hpack
    (PairDeletionOccurrence.deleteData_injective n firstOffset secondOffset hdata)

/-! ## The common horizontal-domino geometry -/

/-- The six forbidden cells surrounding the lower side and lateral ends of
the required horizontal domino in each of `X`, `Y`, and `Z`. -/
private structure DominoFrame (cells : Finset Cell) (anchor : Cell) : Prop where
  left_mem : anchor ∈ cells
  right_mem : cellAt anchor 1 0 ∈ cells
  west_not : cellAt anchor (-1) 0 ∉ cells
  east_not : cellAt anchor 2 0 ∉ cells
  southwest_not : cellAt anchor (-1) (-1) ∉ cells
  leftSouth_not : cellAt anchor 0 (-1) ∉ cells
  rightSouth_not : cellAt anchor 1 (-1) ∉ cells
  southeast_not : cellAt anchor 2 (-1) ∉ cells

private theorem x_occursAt_frame {cells : Finset Cell} {anchor : Cell}
    (h : buiXPattern.OccursAt cells anchor) : DominoFrame cells anchor := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hmem := h.1 (0, 0) (by simp [buiXPattern])
    rw [show anchor + (0, 0) = anchor by
      apply Prod.ext <;> simp] at hmem
    exact hmem
  · exact h.1 (1, 0) (by simp [buiXPattern])
  · exact h.2 (-1, 0) (by simp [buiXPattern])
  · exact h.2 (2, 0) (by simp [buiXPattern])
  · exact h.2 (-1, -1) (by simp [buiXPattern])
  · exact h.2 (0, -1) (by simp [buiXPattern])
  · exact h.2 (1, -1) (by simp [buiXPattern])
  · exact h.2 (2, -1) (by simp [buiXPattern])

private theorem y_occursAt_frame {cells : Finset Cell} {anchor : Cell}
    (h : buiYPattern.OccursAt cells anchor) : DominoFrame cells anchor := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hmem := h.1 (0, 0) (by simp [buiYPattern])
    rw [show anchor + (0, 0) = anchor by
      apply Prod.ext <;> simp] at hmem
    exact hmem
  · exact h.1 (1, 0) (by simp [buiYPattern])
  · exact h.2 (-1, 0) (by simp [buiYPattern])
  · exact h.2 (2, 0) (by simp [buiYPattern])
  · exact h.2 (-1, -1) (by simp [buiYPattern])
  · exact h.2 (0, -1) (by simp [buiYPattern])
  · exact h.2 (1, -1) (by simp [buiYPattern])
  · exact h.2 (2, -1) (by simp [buiYPattern])

private theorem z_occursAt_frame {cells : Finset Cell} {anchor : Cell}
    (h : buiZPattern.OccursAt cells anchor) : DominoFrame cells anchor := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hmem := h.1 (0, 0) (by simp [buiZPattern])
    rw [show anchor + (0, 0) = anchor by
      apply Prod.ext <;> simp] at hmem
    exact hmem
  · exact h.1 (1, 0) (by simp [buiZPattern])
  · exact h.2 (-1, 0) (by simp [buiZPattern])
  · exact h.2 (2, 0) (by simp [buiZPattern])
  · exact h.2 (-1, -1) (by simp [buiZPattern])
  · exact h.2 (0, -1) (by simp [buiZPattern])
  · exact h.2 (1, -1) (by simp [buiZPattern])
  · exact h.2 (2, -1) (by simp [buiZPattern])

private theorem y_northwest_not {cells : Finset Cell} {anchor : Cell}
    (h : buiYPattern.OccursAt cells anchor) :
    cellAt anchor (-1) 1 ∉ cells := by
  exact h.2 (-1, 1) (by simp [buiYPattern])

private theorem z_northwest_not {cells : Finset Cell} {anchor : Cell}
    (h : buiZPattern.OccursAt cells anchor) :
    cellAt anchor (-1) 1 ∉ cells := by
  exact h.2 (-1, 1) (by simp [buiZPattern])

private theorem z_farNortheast_not {cells : Finset Cell} {anchor : Cell}
    (h : buiZPattern.OccursAt cells anchor) :
    cellAt anchor 2 1 ∉ cells := by
  exact h.2 (2, 1) (by simp [buiZPattern])

private theorem left_neighbor_eq_right_or_north {cells : Finset Cell}
    {anchor other : Cell} (frame : DominoFrame cells anchor)
    (hother : other ∈ cells) (hadjacent : EdgeAdjacent anchor other) :
    other = cellAt anchor 1 0 ∨ other = cellAt anchor 0 1 := by
  rcases hadjacent with h | h | h | h
  · left
    calc
      other = (anchor.1 + 1, anchor.2) := h
      _ = cellAt anchor 1 0 := by
        apply Prod.ext <;> dsimp [cellAt] <;> omega
  · exfalso
    apply frame.west_not
    have heq : other = cellAt anchor (-1) 0 := by
      calc
        other = (anchor.1 - 1, anchor.2) := h
        _ = cellAt anchor (-1) 0 := by
          apply Prod.ext <;> dsimp [cellAt] <;> omega
    exact heq ▸ hother
  · right
    calc
      other = (anchor.1, anchor.2 + 1) := h
      _ = cellAt anchor 0 1 := by
        apply Prod.ext <;> dsimp [cellAt] <;> omega
  · exfalso
    apply frame.leftSouth_not
    have heq : other = cellAt anchor 0 (-1) := by
      calc
        other = (anchor.1, anchor.2 - 1) := h
        _ = cellAt anchor 0 (-1) := by
          apply Prod.ext <;> dsimp [cellAt] <;> omega
    exact heq ▸ hother

private theorem right_neighbor_eq_left_or_north {cells : Finset Cell}
    {anchor other : Cell} (frame : DominoFrame cells anchor)
    (hother : other ∈ cells)
    (hadjacent : EdgeAdjacent (cellAt anchor 1 0) other) :
    other = anchor ∨ other = cellAt anchor 1 1 := by
  rcases hadjacent with h | h | h | h
  · exfalso
    apply frame.east_not
    have heq : other = cellAt anchor 2 0 := by
      calc
        other = ((cellAt anchor 1 0).1 + 1, (cellAt anchor 1 0).2) := h
        _ = cellAt anchor 2 0 := by
          apply Prod.ext <;> dsimp [cellAt] <;> omega
    exact heq ▸ hother
  · left
    calc
      other = ((cellAt anchor 1 0).1 - 1, (cellAt anchor 1 0).2) := h
      _ = anchor := by
        apply Prod.ext <;> dsimp [cellAt] <;> omega
  · right
    calc
      other = ((cellAt anchor 1 0).1, (cellAt anchor 1 0).2 + 1) := h
      _ = cellAt anchor 1 1 := by
        apply Prod.ext <;> dsimp [cellAt] <;> omega
  · exfalso
    apply frame.rightSouth_not
    have heq : other = cellAt anchor 1 (-1) := by
      calc
        other = ((cellAt anchor 1 0).1, (cellAt anchor 1 0).2 - 1) := h
        _ = cellAt anchor 1 (-1) := by
          apply Prod.ext <;> dsimp [cellAt] <;> omega
    exact heq ▸ hother

private theorem leftLeaf_of_north_absent {cells : Finset Cell}
    {anchor : Cell} (frame : DominoFrame cells anchor)
    (hnorth : cellAt anchor 0 1 ∉ cells) :
    LeafAt cells anchor (cellAt anchor 1 0) where
  anchor_mem := frame.left_mem
  parent_mem := frame.right_mem
  anchor_ne_parent := (cellAt_right_ne anchor).symm
  only_neighbor := by
    intro other hother hadjacent
    rcases left_neighbor_eq_right_or_north frame hother hadjacent with h | h
    · exact h
    · exact False.elim (hnorth (h ▸ hother))

private theorem rightLeaf_of_northeast_absent {cells : Finset Cell}
    {anchor : Cell} (frame : DominoFrame cells anchor)
    (hnortheast : cellAt anchor 1 1 ∉ cells) :
    LeafAt cells (cellAt anchor 1 0) anchor where
  anchor_mem := frame.right_mem
  parent_mem := frame.left_mem
  anchor_ne_parent := cellAt_right_ne anchor
  only_neighbor := by
    intro other hother hadjacent
    rcases right_neighbor_eq_left_or_north frame hother hadjacent with h | h
    · exact h
    · exact False.elim (hnortheast (h ▸ hother))

/-- If only the upper-left cell is present, delete the lower-right leaf and
then the lower-left leaf. -/
private theorem connected_delete_right_then_left {P : Polyomino}
    {anchor : Cell} (frame : DominoFrame P.cells anchor)
    (hnorth : cellAt anchor 0 1 ∈ P.cells)
    (hnortheast : cellAt anchor 1 1 ∉ P.cells) :
    EdgeConnected
      ((P.cells.erase (cellAt anchor 1 0)).erase anchor) := by
  let rightLeaf := rightLeaf_of_northeast_absent frame hnortheast
  let firstRemainder := P.eraseLeaf (cellAt anchor 1 0) anchor rightLeaf
  have leftLeaf : LeafAt firstRemainder.cells anchor (cellAt anchor 0 1) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Finset.mem_erase.mpr
        ⟨(cellAt_right_ne anchor).symm, frame.left_mem⟩
    · exact Finset.mem_erase.mpr
        ⟨cellAt_north_ne_right anchor, hnorth⟩
    · exact (cellAt_north_ne anchor).symm
    · intro other hother hadjacent
      have hotherOriginal := (Finset.mem_erase.mp hother).2
      rcases left_neighbor_eq_right_or_north frame hotherOriginal hadjacent with h | h
      · exact False.elim ((Finset.mem_erase.mp hother).1 h)
      · exact h
  simpa [firstRemainder, Polyomino.eraseLeaf] using
    (edgeConnected_erase_leaf leftLeaf)

/-- If only the upper-right cell is present, delete the lower-left leaf and
then the lower-right leaf. -/
private theorem connected_delete_left_then_right {P : Polyomino}
    {anchor : Cell} (frame : DominoFrame P.cells anchor)
    (hnorth : cellAt anchor 0 1 ∉ P.cells)
    (hnortheast : cellAt anchor 1 1 ∈ P.cells) :
    EdgeConnected
      ((P.cells.erase anchor).erase (cellAt anchor 1 0)) := by
  let leftLeaf := leftLeaf_of_north_absent frame hnorth
  let firstRemainder := P.eraseLeaf anchor (cellAt anchor 1 0) leftLeaf
  have rightLeaf : LeafAt firstRemainder.cells (cellAt anchor 1 0)
      (cellAt anchor 1 1) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Finset.mem_erase.mpr
        ⟨cellAt_right_ne anchor, frame.right_mem⟩
    · exact Finset.mem_erase.mpr
        ⟨cellAt_northeast_ne_left anchor, hnortheast⟩
    · exact (cellAt_northeast_ne_right anchor).symm
    · intro other hother hadjacent
      have hotherOriginal := (Finset.mem_erase.mp hother).2
      rcases right_neighbor_eq_left_or_north frame hotherOriginal hadjacent with h | h
      · exact False.elim ((Finset.mem_erase.mp hother).1 h)
      · exact h
  simpa [firstRemainder, Polyomino.eraseLeaf] using
    (edgeConnected_erase_leaf rightLeaf)

private def retractLowerDomino (anchor other : Cell) : Cell :=
  if other = cellAt anchor 1 0 then cellAt anchor 1 1
  else if other = anchor then cellAt anchor 0 1
  else other

private theorem retractLowerDomino_right (anchor : Cell) :
    retractLowerDomino anchor (cellAt anchor 1 0) = cellAt anchor 1 1 := by
  simp [retractLowerDomino]

private theorem retractLowerDomino_left (anchor : Cell) :
    retractLowerDomino anchor anchor = cellAt anchor 0 1 := by
  simp [retractLowerDomino, (cellAt_right_ne anchor).symm]

private theorem retractLowerDomino_north (anchor : Cell) :
    retractLowerDomino anchor (cellAt anchor 0 1) = cellAt anchor 0 1 := by
  simp [retractLowerDomino, cellAt_north_ne_right anchor,
    cellAt_north_ne anchor]

private theorem retractLowerDomino_northeast (anchor : Cell) :
    retractLowerDomino anchor (cellAt anchor 1 1) = cellAt anchor 1 1 := by
  simp [retractLowerDomino, cellAt_northeast_ne_right anchor,
    cellAt_northeast_ne_left anchor]

private theorem retractLowerDomino_other {anchor other : Cell}
    (hright : other ≠ cellAt anchor 1 0) (hleft : other ≠ anchor) :
    retractLowerDomino anchor other = other := by
  simp [retractLowerDomino, hright, hleft]

/-- If both upper cells are occupied, their edge replaces the deleted lower
edge.  Retraction of the two lower vertices onto the two upper vertices lifts
every old path to the double-erased set. -/
private theorem connected_delete_both_with_upper_bridge {P : Polyomino}
    {anchor : Cell} (frame : DominoFrame P.cells anchor)
    (hnorth : cellAt anchor 0 1 ∈ P.cells)
    (hnortheast : cellAt anchor 1 1 ∈ P.cells) :
    EdgeConnected
      ((P.cells.erase (cellAt anchor 1 0)).erase anchor) := by
  let remainder := (P.cells.erase (cellAt anchor 1 0)).erase anchor
  have hc : cellAt anchor 0 1 ∈ remainder :=
    Finset.mem_erase.mpr ⟨cellAt_north_ne anchor,
      Finset.mem_erase.mpr ⟨cellAt_north_ne_right anchor, hnorth⟩⟩
  have hd : cellAt anchor 1 1 ∈ remainder :=
    Finset.mem_erase.mpr ⟨cellAt_northeast_ne_left anchor,
      Finset.mem_erase.mpr
        ⟨cellAt_northeast_ne_right anchor, hnortheast⟩⟩
  have hcd : EdgeAdjacent (cellAt anchor 0 1) (cellAt anchor 1 1) := by
    left
    apply Prod.ext <;> simp [cellAt]
  have mapEdge : ∀ {u v : Cell}, EdgeAdjacentIn P.cells u v →
      Relation.ReflTransGen (EdgeAdjacentIn remainder)
        (retractLowerDomino anchor u) (retractLowerDomino anchor v) := by
    intro u v huv
    by_cases huRight : u = cellAt anchor 1 0
    · subst u
      rcases right_neighbor_eq_left_or_north frame huv.2.1 huv.2.2 with hv | hv
      · subst v
        apply Relation.ReflTransGen.single
        rw [retractLowerDomino_right, retractLowerDomino_left]
        exact ⟨hd, hc, edgeAdjacent_symm hcd⟩
      · subst v
        rw [retractLowerDomino_right, retractLowerDomino_northeast]
    · by_cases huLeft : u = anchor
      · subst u
        rcases left_neighbor_eq_right_or_north frame huv.2.1 huv.2.2 with hv | hv
        · subst v
          apply Relation.ReflTransGen.single
          rw [retractLowerDomino_left, retractLowerDomino_right]
          exact ⟨hc, hd, hcd⟩
        · subst v
          rw [retractLowerDomino_left, retractLowerDomino_north]
      · by_cases hvRight : v = cellAt anchor 1 0
        · subst v
          rcases right_neighbor_eq_left_or_north frame huv.1
              (edgeAdjacent_symm huv.2.2) with hu | hu
          · exact False.elim (huLeft hu)
          · subst u
            rw [retractLowerDomino_northeast, retractLowerDomino_right]
        · by_cases hvLeft : v = anchor
          · subst v
            rcases left_neighbor_eq_right_or_north frame huv.1
                (edgeAdjacent_symm huv.2.2) with hu | hu
            · exact False.elim (huRight hu)
            · subst u
              rw [retractLowerDomino_north, retractLowerDomino_left]
          · apply Relation.ReflTransGen.single
            rw [retractLowerDomino_other huRight huLeft,
              retractLowerDomino_other hvRight hvLeft]
            exact ⟨Finset.mem_erase.mpr ⟨huLeft,
                Finset.mem_erase.mpr ⟨huRight, huv.1⟩⟩,
              Finset.mem_erase.mpr ⟨hvLeft,
                Finset.mem_erase.mpr ⟨hvRight, huv.2.1⟩⟩,
              huv.2.2⟩
  intro x hx y hy
  have hxErase := Finset.mem_erase.mp hx
  have hxErase' := Finset.mem_erase.mp hxErase.2
  have hyErase := Finset.mem_erase.mp hy
  have hyErase' := Finset.mem_erase.mp hyErase.2
  have hpath := P.edgeConnected x hxErase'.2 y hyErase'.2
  have hlift := hpath.lift' (retractLowerDomino anchor)
    (fun _ _ hstep => mapEdge hstep)
  change Relation.ReflTransGen (EdgeAdjacentIn remainder)
    (retractLowerDomino anchor x) (retractLowerDomino anchor y) at hlift
  rw [retractLowerDomino_other hxErase'.1 hxErase.1,
    retractLowerDomino_other hyErase'.1 hyErase.1] at hlift
  exact hlift

/-! ## Canonical deletion packages for the three occupancy cases -/

private def westOffset : Cell := (-1, 0)
private def eastOffset : Cell := (1, 0)
private def southwestOffset : Cell := (-1, -1)
private def southOffset : Cell := (0, -1)
private def southeastOffset : Cell := (1, -1)

private theorem leftUpper_add_southeast (anchor : Cell) :
    cellAt anchor 0 1 + southeastOffset = cellAt anchor 1 0 := by
  apply Prod.ext <;> dsimp [cellAt, southeastOffset] <;> omega

private theorem leftUpper_add_south (anchor : Cell) :
    cellAt anchor 0 1 + southOffset = anchor := by
  apply Prod.ext <;> dsimp [cellAt, southOffset] <;> omega

private theorem rightUpper_add_southwest (anchor : Cell) :
    cellAt anchor 1 1 + southwestOffset = anchor := by
  apply Prod.ext <;> dsimp [cellAt, southwestOffset] <;> omega

private theorem rightUpper_add_south (anchor : Cell) :
    cellAt anchor 1 1 + southOffset = cellAt anchor 1 0 := by
  apply Prod.ext <;> dsimp [cellAt, southOffset] <;> omega

private def deleteLeftLeaf {n : ℕ} (P : NormalizedPolyomino n)
    (anchor : Cell) (frame : DominoFrame P.toPolyomino.cells anchor)
    (hnorth : cellAt anchor 0 1 ∉ P.toPolyomino.cells) :
    LeafDeletionOccurrence n westOffset where
  polyomino := P
  anchor := anchor
  parent := cellAt anchor 1 0
  anchor_eq := by
    apply Prod.ext <;> simp [cellAt, westOffset]
  leaf := leftLeaf_of_north_absent frame hnorth

private def deleteRightLeaf {n : ℕ} (P : NormalizedPolyomino n)
    (anchor : Cell) (frame : DominoFrame P.toPolyomino.cells anchor)
    (hnortheast : cellAt anchor 1 1 ∉ P.toPolyomino.cells) :
    LeafDeletionOccurrence n eastOffset where
  polyomino := P
  anchor := cellAt anchor 1 0
  parent := anchor
  anchor_eq := by
    apply Prod.ext <;> simp [cellAt, eastOffset]
  leaf := rightLeaf_of_northeast_absent frame hnortheast

/-- Delete lower right and then lower left, retaining the upper-left cell. -/
private def deletePairMarkLeftUpper {n : ℕ} (P : NormalizedPolyomino n)
    (anchor : Cell) (frame : DominoFrame P.toPolyomino.cells anchor)
    (hnorth : cellAt anchor 0 1 ∈ P.toPolyomino.cells)
    (hconnected : EdgeConnected
      ((P.toPolyomino.cells.erase (cellAt anchor 1 0)).erase anchor)) :
    PairDeletionOccurrence n southeastOffset southOffset where
  polyomino := P
  mark := cellAt anchor 0 1
  mark_mem := hnorth
  first_mem := by
    rw [leftUpper_add_southeast]
    exact frame.right_mem
  second_mem := by
    rw [leftUpper_add_south]
    exact frame.left_mem
  first_ne_second := by
    intro h
    have h' := congrArg Prod.fst h
    dsimp [cellAt, southeastOffset, southOffset] at h'
    omega
  mark_ne_first := by
    intro h
    have h' := congrArg Prod.fst h
    dsimp [cellAt, southeastOffset] at h'
    omega
  mark_ne_second := by
    intro h
    have h' := congrArg Prod.snd h
    dsimp [cellAt, southOffset] at h'
    omega
  connected := by
    rw [leftUpper_add_southeast, leftUpper_add_south]
    exact hconnected

/-- Delete lower left and then lower right, retaining the upper-right cell. -/
private def deletePairMarkRightUpper {n : ℕ} (P : NormalizedPolyomino n)
    (anchor : Cell) (frame : DominoFrame P.toPolyomino.cells anchor)
    (hnortheast : cellAt anchor 1 1 ∈ P.toPolyomino.cells)
    (hconnected : EdgeConnected
      ((P.toPolyomino.cells.erase anchor).erase (cellAt anchor 1 0))) :
    PairDeletionOccurrence n southwestOffset southOffset where
  polyomino := P
  mark := cellAt anchor 1 1
  mark_mem := hnortheast
  first_mem := by
    rw [rightUpper_add_southwest]
    exact frame.left_mem
  second_mem := by
    rw [rightUpper_add_south]
    exact frame.right_mem
  first_ne_second := by
    intro h
    have h' := congrArg Prod.fst h
    dsimp [cellAt, southwestOffset, southOffset] at h'
    omega
  mark_ne_first := by
    intro h
    have h' := congrArg Prod.snd h
    dsimp [cellAt, southwestOffset] at h'
    omega
  mark_ne_second := by
    intro h
    have h' := congrArg Prod.snd h
    dsimp [cellAt, southOffset] at h'
    omega
  connected := by
    rw [rightUpper_add_southwest, rightUpper_add_south]
    exact hconnected

private theorem mem_pairErase_original {cells : Finset Cell} {first second c : Cell}
    (h : c ∈ (cells.erase first).erase second) : c ∈ cells :=
  (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2

private theorem first_ne_of_mem_pairErase {cells : Finset Cell}
    {first second c : Cell} (h : c ∈ (cells.erase first).erase second) :
    c ≠ first :=
  (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).1

private theorem second_ne_of_mem_pairErase {cells : Finset Cell}
    {first second c : Cell} (h : c ∈ (cells.erase first).erase second) :
    c ≠ second :=
  (Finset.mem_erase.mp h).1

private theorem not_mem_erase_of_not_mem {cells : Finset Cell} {a c : Cell}
    (h : c ∉ cells) : c ∉ cells.erase a :=
  fun hc => h (Finset.mem_erase.mp hc).2

private theorem erased_cell_not_mem (cells : Finset Cell) (a : Cell) :
    a ∉ cells.erase a := by simp

private theorem not_mem_pairErase_of_not_mem {cells : Finset Cell}
    {first second c : Cell} (h : c ∉ cells) :
    c ∉ (cells.erase first).erase second :=
  fun hc => h (mem_pairErase_original hc)

private theorem first_not_mem_pairErase (cells : Finset Cell)
    (first second : Cell) : first ∉ (cells.erase first).erase second :=
  fun h => (first_ne_of_mem_pairErase h) rfl

private theorem second_not_mem_pairErase (cells : Finset Cell)
    (first second : Cell) : second ∉ (cells.erase first).erase second :=
  fun h => (second_ne_of_mem_pairErase h) rfl

private theorem mem_pairErase_of_mem {cells : Finset Cell}
    {first second c : Cell} (hc : c ∈ cells)
    (hcfirst : c ≠ first) (hcsecond : c ≠ second) :
    c ∈ (cells.erase first).erase second :=
  Finset.mem_erase.mpr ⟨hcsecond,
    Finset.mem_erase.mpr ⟨hcfirst, hc⟩⟩

/-! ## The eight raw local pattern transformations -/

private theorem x_delete_left_occursAt_d {cells : Finset Cell}
    {anchor : Cell} (h : buiXPattern.OccursAt cells anchor)
    (hnorth : cellAt anchor 0 1 ∉ cells) :
    buiDPattern.OccursAt (cells.erase anchor) (cellAt anchor 1 0) := by
  let frame := x_occursAt_frame h
  constructor
  · intro offset hoffset
    have hoffset' : offset = (0, 0) := by
      simpa [buiDPattern] using hoffset
    subst offset
    rw [show cellAt anchor 1 0 + (0, 0) = cellAt anchor 1 0 by
      apply Prod.ext <;> dsimp [cellAt] <;> omega]
    exact Finset.mem_erase.mpr
      ⟨cellAt_right_ne anchor, frame.right_mem⟩
  · intro offset hoffset
    simp only [buiDPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with hoffset | hoffset | hoffset | hoffset | hoffset | hoffset
    · subst offset
      rw [show cellAt anchor 1 0 + (-1, 1) = cellAt anchor 0 1 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_erase_of_not_mem hnorth
    · subst offset
      rw [show cellAt anchor 1 0 + (-1, 0) = anchor by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact erased_cell_not_mem cells anchor
    · subst offset
      rw [show cellAt anchor 1 0 + (1, 0) = cellAt anchor 2 0 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_erase_of_not_mem frame.east_not
    · subst offset
      rw [show cellAt anchor 1 0 + (-1, -1) = cellAt anchor 0 (-1) by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_erase_of_not_mem frame.leftSouth_not
    · subst offset
      rw [show cellAt anchor 1 0 + (0, -1) = cellAt anchor 1 (-1) by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_erase_of_not_mem frame.rightSouth_not
    · subst offset
      rw [show cellAt anchor 1 0 + (1, -1) = cellAt anchor 2 (-1) by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_erase_of_not_mem frame.southeast_not

private theorem y_delete_right_occursAt_c {cells : Finset Cell}
    {anchor : Cell} (h : buiYPattern.OccursAt cells anchor)
    (hnortheast : cellAt anchor 1 1 ∉ cells) :
    buiCPattern.OccursAt (cells.erase (cellAt anchor 1 0)) anchor := by
  let frame := y_occursAt_frame h
  constructor
  · intro offset hoffset
    have hoffset' : offset = (0, 0) := by
      simpa [buiCPattern] using hoffset
    subst offset
    rw [show anchor + (0, 0) = anchor by
      apply Prod.ext <;> dsimp <;> omega]
    exact Finset.mem_erase.mpr
      ⟨(cellAt_right_ne anchor).symm, frame.left_mem⟩
  · intro offset hoffset
    simp only [buiCPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with hoffset | hoffset | hoffset | hoffset |
      hoffset | hoffset | hoffset
    · subst offset
      rw [show anchor + (-1, 1) = cellAt anchor (-1) 1 by rfl]
      exact not_mem_erase_of_not_mem (y_northwest_not h)
    · subst offset
      rw [show anchor + (1, 1) = cellAt anchor 1 1 by rfl]
      exact not_mem_erase_of_not_mem hnortheast
    · subst offset
      rw [show anchor + (-1, 0) = cellAt anchor (-1) 0 by rfl]
      exact not_mem_erase_of_not_mem frame.west_not
    · subst offset
      rw [show anchor + (1, 0) = cellAt anchor 1 0 by rfl]
      exact erased_cell_not_mem cells (cellAt anchor 1 0)
    · subst offset
      rw [show anchor + (-1, -1) = cellAt anchor (-1) (-1) by rfl]
      exact not_mem_erase_of_not_mem frame.southwest_not
    · subst offset
      rw [show anchor + (0, -1) = cellAt anchor 0 (-1) by rfl]
      exact not_mem_erase_of_not_mem frame.leftSouth_not
    · subst offset
      rw [show anchor + (1, -1) = cellAt anchor 1 (-1) by rfl]
      exact not_mem_erase_of_not_mem frame.rightSouth_not

private theorem z_delete_left_occursAt_c {cells : Finset Cell}
    {anchor : Cell} (h : buiZPattern.OccursAt cells anchor)
    (hnorth : cellAt anchor 0 1 ∉ cells) :
    buiCPattern.OccursAt (cells.erase anchor) (cellAt anchor 1 0) := by
  let frame := z_occursAt_frame h
  constructor
  · intro offset hoffset
    have hoffset' : offset = (0, 0) := by
      simpa [buiCPattern] using hoffset
    subst offset
    rw [show cellAt anchor 1 0 + (0, 0) = cellAt anchor 1 0 by
      apply Prod.ext <;> dsimp [cellAt] <;> omega]
    exact Finset.mem_erase.mpr
      ⟨cellAt_right_ne anchor, frame.right_mem⟩
  · intro offset hoffset
    simp only [buiCPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with hoffset | hoffset | hoffset | hoffset |
      hoffset | hoffset | hoffset
    · subst offset
      rw [show cellAt anchor 1 0 + (-1, 1) = cellAt anchor 0 1 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_erase_of_not_mem hnorth
    · subst offset
      rw [show cellAt anchor 1 0 + (1, 1) = cellAt anchor 2 1 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_erase_of_not_mem (z_farNortheast_not h)
    · subst offset
      rw [show cellAt anchor 1 0 + (-1, 0) = anchor by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact erased_cell_not_mem cells anchor
    · subst offset
      rw [show cellAt anchor 1 0 + (1, 0) = cellAt anchor 2 0 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_erase_of_not_mem frame.east_not
    · subst offset
      rw [show cellAt anchor 1 0 + (-1, -1) = cellAt anchor 0 (-1) by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_erase_of_not_mem frame.leftSouth_not
    · subst offset
      rw [show cellAt anchor 1 0 + (0, -1) = cellAt anchor 1 (-1) by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_erase_of_not_mem frame.rightSouth_not
    · subst offset
      rw [show cellAt anchor 1 0 + (1, -1) = cellAt anchor 2 (-1) by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_erase_of_not_mem frame.southeast_not

/-- The horizontally reflected orientation of `G`. -/
private def rightGPattern : OffsetPattern where
  required := {(0, 0)}
  forbidden := {(1, 0), (-1, -1), (0, -1), (1, -1)}

private theorem x_delete_pair_left_only_occursAt_rightG
    {cells : Finset Cell} {anchor : Cell}
    (h : buiXPattern.OccursAt cells anchor)
    (hnorth : cellAt anchor 0 1 ∈ cells)
    (hnortheast : cellAt anchor 1 1 ∉ cells) :
    rightGPattern.OccursAt
      ((cells.erase (cellAt anchor 1 0)).erase anchor)
      (cellAt anchor 0 1) := by
  let frame := x_occursAt_frame h
  constructor
  · intro offset hoffset
    have hoffset' : offset = (0, 0) := by
      simpa [rightGPattern] using hoffset
    subst offset
    rw [show cellAt anchor 0 1 + (0, 0) = cellAt anchor 0 1 by
      apply Prod.ext <;> dsimp [cellAt] <;> omega]
    exact mem_pairErase_of_mem hnorth
      (cellAt_north_ne_right anchor) (cellAt_north_ne anchor)
  · intro offset hoffset
    simp only [rightGPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with hoffset | hoffset | hoffset | hoffset
    · subst offset
      rw [show cellAt anchor 0 1 + (1, 0) = cellAt anchor 1 1 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_pairErase_of_not_mem hnortheast
    · subst offset
      rw [show cellAt anchor 0 1 + (-1, -1) = cellAt anchor (-1) 0 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_pairErase_of_not_mem frame.west_not
    · subst offset
      rw [show cellAt anchor 0 1 + (0, -1) = anchor by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact second_not_mem_pairErase cells (cellAt anchor 1 0) anchor
    · subst offset
      rw [show cellAt anchor 0 1 + (1, -1) = cellAt anchor 1 0 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact first_not_mem_pairErase cells (cellAt anchor 1 0) anchor

private theorem x_delete_pair_both_occursAt_u {cells : Finset Cell}
    {anchor : Cell} (h : buiXPattern.OccursAt cells anchor)
    (hnorth : cellAt anchor 0 1 ∈ cells)
    (hnortheast : cellAt anchor 1 1 ∈ cells) :
    buiUPattern.OccursAt
      ((cells.erase (cellAt anchor 1 0)).erase anchor)
      (cellAt anchor 0 1) := by
  let frame := x_occursAt_frame h
  constructor
  · intro offset hoffset
    simp only [buiUPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with hoffset | hoffset
    · subst offset
      rw [show cellAt anchor 0 1 + (0, 0) = cellAt anchor 0 1 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact mem_pairErase_of_mem hnorth
        (cellAt_north_ne_right anchor) (cellAt_north_ne anchor)
    · subst offset
      rw [show cellAt anchor 0 1 + (1, 0) = cellAt anchor 1 1 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact mem_pairErase_of_mem hnortheast
        (cellAt_northeast_ne_right anchor)
        (cellAt_northeast_ne_left anchor)
  · intro offset hoffset
    simp only [buiUPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with hoffset | hoffset | hoffset | hoffset
    · subst offset
      rw [show cellAt anchor 0 1 + (-1, -1) = cellAt anchor (-1) 0 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_pairErase_of_not_mem frame.west_not
    · subst offset
      rw [show cellAt anchor 0 1 + (0, -1) = anchor by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact second_not_mem_pairErase cells (cellAt anchor 1 0) anchor
    · subst offset
      rw [show cellAt anchor 0 1 + (1, -1) = cellAt anchor 1 0 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact first_not_mem_pairErase cells (cellAt anchor 1 0) anchor
    · subst offset
      rw [show cellAt anchor 0 1 + (2, -1) = cellAt anchor 2 0 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_pairErase_of_not_mem frame.east_not

private theorem y_delete_pair_right_only_occursAt_g
    {cells : Finset Cell} {anchor : Cell}
    (h : buiYPattern.OccursAt cells anchor)
    (hnorth : cellAt anchor 0 1 ∉ cells)
    (hnortheast : cellAt anchor 1 1 ∈ cells) :
    buiGPattern.OccursAt
      ((cells.erase anchor).erase (cellAt anchor 1 0))
      (cellAt anchor 1 1) := by
  let frame := y_occursAt_frame h
  constructor
  · intro offset hoffset
    have hoffset' : offset = (0, 0) := by
      simpa [buiGPattern] using hoffset
    subst offset
    rw [show cellAt anchor 1 1 + (0, 0) = cellAt anchor 1 1 by
      apply Prod.ext <;> dsimp [cellAt] <;> omega]
    exact mem_pairErase_of_mem hnortheast
      (cellAt_northeast_ne_left anchor)
      (cellAt_northeast_ne_right anchor)
  · intro offset hoffset
    simp only [buiGPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with hoffset | hoffset | hoffset | hoffset
    · subst offset
      rw [show cellAt anchor 1 1 + (-1, 0) = cellAt anchor 0 1 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_pairErase_of_not_mem hnorth
    · subst offset
      rw [show cellAt anchor 1 1 + (-1, -1) = anchor by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact first_not_mem_pairErase cells anchor (cellAt anchor 1 0)
    · subst offset
      rw [show cellAt anchor 1 1 + (0, -1) = cellAt anchor 1 0 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact second_not_mem_pairErase cells anchor (cellAt anchor 1 0)
    · subst offset
      rw [show cellAt anchor 1 1 + (1, -1) = cellAt anchor 2 0 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_pairErase_of_not_mem frame.east_not

private theorem y_delete_pair_both_occursAt_t {cells : Finset Cell}
    {anchor : Cell} (h : buiYPattern.OccursAt cells anchor)
    (hnorth : cellAt anchor 0 1 ∈ cells)
    (hnortheast : cellAt anchor 1 1 ∈ cells) :
    buiTPattern.OccursAt
      ((cells.erase (cellAt anchor 1 0)).erase anchor)
      (cellAt anchor 0 1) := by
  let frame := y_occursAt_frame h
  constructor
  · intro offset hoffset
    simp only [buiTPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with hoffset | hoffset
    · subst offset
      rw [show cellAt anchor 0 1 + (0, 0) = cellAt anchor 0 1 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact mem_pairErase_of_mem hnorth
        (cellAt_north_ne_right anchor) (cellAt_north_ne anchor)
    · subst offset
      rw [show cellAt anchor 0 1 + (1, 0) = cellAt anchor 1 1 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact mem_pairErase_of_mem hnortheast
        (cellAt_northeast_ne_right anchor)
        (cellAt_northeast_ne_left anchor)
  · intro offset hoffset
    simp only [buiTPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with hoffset | hoffset | hoffset | hoffset | hoffset
    · subst offset
      rw [show cellAt anchor 0 1 + (-1, 0) = cellAt anchor (-1) 1 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_pairErase_of_not_mem (y_northwest_not h)
    · subst offset
      rw [show cellAt anchor 0 1 + (-1, -1) = cellAt anchor (-1) 0 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_pairErase_of_not_mem frame.west_not
    · subst offset
      rw [show cellAt anchor 0 1 + (0, -1) = anchor by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact second_not_mem_pairErase cells (cellAt anchor 1 0) anchor
    · subst offset
      rw [show cellAt anchor 0 1 + (1, -1) = cellAt anchor 1 0 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact first_not_mem_pairErase cells (cellAt anchor 1 0) anchor
    · subst offset
      rw [show cellAt anchor 0 1 + (2, -1) = cellAt anchor 2 0 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_pairErase_of_not_mem frame.east_not

private theorem z_delete_pair_left_only_occursAt_e
    {cells : Finset Cell} {anchor : Cell}
    (h : buiZPattern.OccursAt cells anchor)
    (hnorth : cellAt anchor 0 1 ∈ cells)
    (hnortheast : cellAt anchor 1 1 ∉ cells) :
    buiEPattern.OccursAt
      ((cells.erase (cellAt anchor 1 0)).erase anchor)
      (cellAt anchor 0 1) := by
  let frame := z_occursAt_frame h
  constructor
  · intro offset hoffset
    have hoffset' : offset = (0, 0) := by
      simpa [buiEPattern] using hoffset
    subst offset
    rw [show cellAt anchor 0 1 + (0, 0) = cellAt anchor 0 1 by
      apply Prod.ext <;> dsimp [cellAt] <;> omega]
    exact mem_pairErase_of_mem hnorth
      (cellAt_north_ne_right anchor) (cellAt_north_ne anchor)
  · intro offset hoffset
    simp only [buiEPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with hoffset | hoffset | hoffset | hoffset | hoffset
    · subst offset
      rw [show cellAt anchor 0 1 + (-1, 0) = cellAt anchor (-1) 1 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_pairErase_of_not_mem (z_northwest_not h)
    · subst offset
      rw [show cellAt anchor 0 1 + (1, 0) = cellAt anchor 1 1 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_pairErase_of_not_mem hnortheast
    · subst offset
      rw [show cellAt anchor 0 1 + (-1, -1) = cellAt anchor (-1) 0 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_pairErase_of_not_mem frame.west_not
    · subst offset
      rw [show cellAt anchor 0 1 + (0, -1) = anchor by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact second_not_mem_pairErase cells (cellAt anchor 1 0) anchor
    · subst offset
      rw [show cellAt anchor 0 1 + (1, -1) = cellAt anchor 1 0 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact first_not_mem_pairErase cells (cellAt anchor 1 0) anchor

private theorem z_delete_pair_both_occursAt_x {cells : Finset Cell}
    {anchor : Cell} (h : buiZPattern.OccursAt cells anchor)
    (hnorth : cellAt anchor 0 1 ∈ cells)
    (hnortheast : cellAt anchor 1 1 ∈ cells) :
    buiXPattern.OccursAt
      ((cells.erase (cellAt anchor 1 0)).erase anchor)
      (cellAt anchor 0 1) := by
  let frame := z_occursAt_frame h
  constructor
  · intro offset hoffset
    simp only [buiXPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with hoffset | hoffset
    · subst offset
      rw [show cellAt anchor 0 1 + (0, 0) = cellAt anchor 0 1 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact mem_pairErase_of_mem hnorth
        (cellAt_north_ne_right anchor) (cellAt_north_ne anchor)
    · subst offset
      rw [show cellAt anchor 0 1 + (1, 0) = cellAt anchor 1 1 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact mem_pairErase_of_mem hnortheast
        (cellAt_northeast_ne_right anchor)
        (cellAt_northeast_ne_left anchor)
  · intro offset hoffset
    simp only [buiXPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with hoffset | hoffset | hoffset | hoffset |
      hoffset | hoffset
    · subst offset
      rw [show cellAt anchor 0 1 + (-1, 0) = cellAt anchor (-1) 1 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_pairErase_of_not_mem (z_northwest_not h)
    · subst offset
      rw [show cellAt anchor 0 1 + (2, 0) = cellAt anchor 2 1 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_pairErase_of_not_mem (z_farNortheast_not h)
    · subst offset
      rw [show cellAt anchor 0 1 + (-1, -1) = cellAt anchor (-1) 0 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_pairErase_of_not_mem frame.west_not
    · subst offset
      rw [show cellAt anchor 0 1 + (0, -1) = anchor by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact second_not_mem_pairErase cells (cellAt anchor 1 0) anchor
    · subst offset
      rw [show cellAt anchor 0 1 + (1, -1) = cellAt anchor 1 0 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact first_not_mem_pairErase cells (cellAt anchor 1 0) anchor
    · subst offset
      rw [show cellAt anchor 0 1 + (2, -1) = cellAt anchor 2 0 by
        apply Prod.ext <;> dsimp [cellAt] <;> omega]
      exact not_mem_pairErase_of_not_mem frame.east_not

/-! ## Horizontal reflection for the asymmetric middle `X` branch -/

private def mirrorCell (cell : Cell) : Cell := (-cell.1, cell.2)

@[simp]
private theorem mirrorCell_involutive (cell : Cell) :
    mirrorCell (mirrorCell cell) = cell := by
  apply Prod.ext <;> simp [mirrorCell]

private theorem mirrorCell_add (a b : Cell) :
    mirrorCell (a + b) = mirrorCell a + mirrorCell b := by
  apply Prod.ext <;> dsimp [mirrorCell] <;> omega

private theorem mirrorCell_injective : Function.Injective mirrorCell := by
  intro a b h
  have h' := congrArg mirrorCell h
  simpa using h'

private theorem edgeAdjacent_mirror {a b : Cell} (h : EdgeAdjacent a b) :
    EdgeAdjacent (mirrorCell a) (mirrorCell b) := by
  rcases h with h | h | h | h <;> subst b
  · right; left
    apply Prod.ext <;> dsimp [mirrorCell] <;> omega
  · left
    apply Prod.ext <;> dsimp [mirrorCell] <;> omega
  · right; right; left
    apply Prod.ext <;> dsimp [mirrorCell] <;> omega
  · right; right; right
    apply Prod.ext <;> dsimp [mirrorCell] <;> omega

private theorem edgeConnected_image_mirror {cells : Finset Cell}
    (hconnected : EdgeConnected cells) :
    EdgeConnected (cells.image mirrorCell) := by
  intro a ha b hb
  rcases Finset.mem_image.mp ha with ⟨a₀, ha₀, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨b₀, hb₀, rfl⟩
  apply Relation.ReflTransGen.lift mirrorCell (r := EdgeAdjacentIn cells)
  · intro x y hxy
    exact ⟨Finset.mem_image.mpr ⟨x, hxy.1, rfl⟩,
      Finset.mem_image.mpr ⟨y, hxy.2.1, rfl⟩,
      edgeAdjacent_mirror hxy.2.2⟩
  · exact hconnected a₀ ha₀ b₀ hb₀

private def Polyomino.mirror (P : Polyomino) : Polyomino where
  cells := P.cells.image mirrorCell
  nonempty := P.nonempty.image mirrorCell
  edgeConnected := edgeConnected_image_mirror P.edgeConnected

@[simp]
private theorem Polyomino.cells_mirror (P : Polyomino) :
    P.mirror.cells = P.cells.image mirrorCell := rfl

private theorem Polyomino.mirror_mirror (P : Polyomino) :
    P.mirror.mirror = P := by
  apply Polyomino.ext
  simp only [Polyomino.cells_mirror, Finset.image_image]
  have hfunctions : mirrorCell ∘ mirrorCell = id := by
    funext cell
    exact mirrorCell_involutive cell
  rw [hfunctions]
  simp

private theorem Polyomino.mirror_translate (P : Polyomino) (v : Cell) :
    (P.translate v).mirror = P.mirror.translate (mirrorCell v) := by
  apply Polyomino.ext
  simp only [Polyomino.cells_mirror, Polyomino.cells_translate,
    Finset.image_image]
  apply Finset.image_congr
  intro cell hcell
  simp [Function.comp_apply, mirrorCell_add]

private def FixedSizePolyomino.mirror {n : ℕ} (P : FixedSizePolyomino n) :
    FixedSizePolyomino n where
  toPolyomino := P.toPolyomino.mirror
  card_cells := by
    change (P.toPolyomino.cells.image mirrorCell).card = n
    rw [Finset.card_image_of_injective _ mirrorCell_injective,
      P.card_cells]

private noncomputable def NormalizedPolyomino.normalizedMirror {n : ℕ}
    (P : NormalizedPolyomino n) : NormalizedPolyomino n :=
  P.toFixedSize.mirror.normalize

private noncomputable def mirrorNormalizationVector {n : ℕ}
    (P : NormalizedPolyomino n) : Cell :=
  -P.toPolyomino.mirror.southwestAnchor

private theorem NormalizedPolyomino.normalizedMirror_injective {n : ℕ} :
    Function.Injective
      (NormalizedPolyomino.normalizedMirror :
        NormalizedPolyomino n → NormalizedPolyomino n) := by
  intro P Q hPQ
  have hpoly := congrArg NormalizedPolyomino.toPolyomino hPQ
  change P.toPolyomino.mirror.translate (mirrorNormalizationVector P) =
    Q.toPolyomino.mirror.translate (mirrorNormalizationVector Q) at hpoly
  have hmirrored := congrArg Polyomino.mirror hpoly
  rw [Polyomino.mirror_translate, Polyomino.mirror_translate,
    Polyomino.mirror_mirror, Polyomino.mirror_mirror] at hmirrored
  have hnormalized := congrArg Polyomino.normalize hmirrored
  rw [Polyomino.normalize_translate, Polyomino.normalize_translate,
    P.normalize_toPolyomino, Q.normalize_toPolyomino] at hnormalized
  exact NormalizedPolyomino.ext hnormalized

private theorem rightG_occursAt_mirror {cells : Finset Cell} {anchor : Cell}
    (h : rightGPattern.OccursAt cells anchor) :
    buiGPattern.OccursAt (cells.image mirrorCell) (mirrorCell anchor) := by
  constructor
  · intro offset hoffset
    have hoffset' : offset = (0, 0) := by
      simpa [buiGPattern] using hoffset
    subst offset
    apply Finset.mem_image.mpr
    refine ⟨anchor, ?_, ?_⟩
    · have hanchor := h.1 (0, 0) (by simp [rightGPattern])
      convert hanchor using 1
      apply Prod.ext <;> simp
    · apply Prod.ext <;> simp [mirrorCell]
  · intro offset hoffset hmem
    rcases Finset.mem_image.mp hmem with ⟨cell, hcell, hcellEq⟩
    simp only [buiGPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with hoffset | hoffset | hoffset | hoffset
    · subst offset
      apply h.2 (1, 0) (by simp [rightGPattern])
      have hc : cell = anchor + (1, 0) := by
        apply mirrorCell_injective
        calc
          mirrorCell cell = mirrorCell anchor + (-1, 0) := hcellEq
          _ = mirrorCell (anchor + (1, 0)) := by
            rw [mirrorCell_add]
            apply Prod.ext <;> simp [mirrorCell]
      exact hc ▸ hcell
    · subst offset
      apply h.2 (1, -1) (by simp [rightGPattern])
      have hc : cell = anchor + (1, -1) := by
        apply mirrorCell_injective
        calc
          mirrorCell cell = mirrorCell anchor + (-1, -1) := hcellEq
          _ = mirrorCell (anchor + (1, -1)) := by
            rw [mirrorCell_add]
            apply Prod.ext <;> simp [mirrorCell]
      exact hc ▸ hcell
    · subst offset
      apply h.2 (0, -1) (by simp [rightGPattern])
      have hc : cell = anchor + (0, -1) := by
        apply mirrorCell_injective
        calc
          mirrorCell cell = mirrorCell anchor + (0, -1) := hcellEq
          _ = mirrorCell (anchor + (0, -1)) := by
            rw [mirrorCell_add]
            apply Prod.ext <;> simp [mirrorCell]
      exact hc ▸ hcell
    · subst offset
      apply h.2 (-1, -1) (by simp [rightGPattern])
      have hc : cell = anchor + (-1, -1) := by
        apply mirrorCell_injective
        calc
          mirrorCell cell = mirrorCell anchor + (1, -1) := hcellEq
          _ = mirrorCell (anchor + (-1, -1)) := by
            rw [mirrorCell_add]
            apply Prod.ext <;> simp [mirrorCell]
      exact hc ▸ hcell

private noncomputable def mirrorMarkedG {n : ℕ}
    (P : NormalizedPolyomino n) (anchor : Cell)
    (h : rightGPattern.OccursAt P.toPolyomino.cells anchor) :
    MarkedOccurrence BuiNeighborhood.g n := by
  classical
  let v := mirrorNormalizationVector P
  let target := P.normalizedMirror
  let mark := v + mirrorCell anchor
  refine ⟨target, ⟨mark, ?_⟩⟩
  rw [OffsetPattern.occurrenceAnchors, Finset.mem_filter]
  have hraw := rightG_occursAt_mirror h
  have hanchor : anchor ∈ P.toPolyomino.cells := by
    have hanchor' := h.1 (0, 0) (by simp [rightGPattern])
    convert hanchor' using 1
    apply Prod.ext <;> simp
  constructor
  · change mark ∈ (P.toPolyomino.cells.image mirrorCell).image
      (fun cell => v + cell)
    exact Finset.mem_image.mpr ⟨mirrorCell anchor,
      Finset.mem_image.mpr ⟨anchor, hanchor, rfl⟩, rfl⟩
  · change buiGPattern.OccursAt
      ((P.toPolyomino.cells.image mirrorCell).image (fun cell => v + cell))
      (v + mirrorCell anchor)
    exact hraw.translate v

private theorem mirrorMarkedG_injective_on_data {n : ℕ}
    {P Q : NormalizedPolyomino n} {anchor other : Cell}
    {hP : rightGPattern.OccursAt P.toPolyomino.cells anchor}
    {hQ : rightGPattern.OccursAt Q.toPolyomino.cells other}
    (heq : mirrorMarkedG P anchor hP = mirrorMarkedG Q other hQ) :
    P = Q ∧ anchor = other := by
  have hpoly : P.normalizedMirror = Q.normalizedMirror :=
    congrArg (fun z : MarkedOccurrence BuiNeighborhood.g n => z.1) heq
  have hPpoly : P = Q :=
    NormalizedPolyomino.normalizedMirror_injective hpoly
  subst Q
  have hmark := congrArg (fun z : MarkedOccurrence BuiNeighborhood.g n =>
    z.2.1) heq
  change mirrorNormalizationVector P + mirrorCell anchor =
    mirrorNormalizationVector P + mirrorCell other at hmark
  have hmirror : mirrorCell anchor = mirrorCell other := add_left_cancel hmark
  exact ⟨rfl, mirrorCell_injective hmirror⟩

/-! ## A reusable three-way finite partition -/

private noncomputable def threeWayMap {α β γ δ : Type}
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (first : {x // ¬p x} → β)
    (second : {x // p x ∧ ¬q x} → γ)
    (third : {x // p x ∧ q x} → δ) :
    α → β ⊕ (γ ⊕ δ) := fun x =>
  if hp : p x then
    if hq : q x then Sum.inr (Sum.inr (third ⟨x, hp, hq⟩))
    else Sum.inr (Sum.inl (second ⟨x, hp, hq⟩))
  else Sum.inl (first ⟨x, hp⟩)

private theorem threeWayMap_injective {α β γ δ : Type}
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (first : {x // ¬p x} → β)
    (second : {x // p x ∧ ¬q x} → γ)
    (third : {x // p x ∧ q x} → δ)
    (hfirst : Function.Injective first)
    (hsecond : Function.Injective second)
    (hthird : Function.Injective third) :
    Function.Injective (threeWayMap p q first second third) := by
  intro x y hxy
  by_cases hpx : p x
  · by_cases hpy : p y
    · by_cases hqx : q x
      · by_cases hqy : q y
        · have hbranch : third ⟨x, hpx, hqx⟩ = third ⟨y, hpy, hqy⟩ := by
            simpa [threeWayMap, hpx, hpy, hqx, hqy] using hxy
          exact congrArg Subtype.val (hthird hbranch)
        · have hxy' := hxy
          simp only [threeWayMap, dif_pos hpx, dif_pos hpy,
            dif_pos hqx, dif_neg hqy] at hxy'
          cases hxy'
      · by_cases hqy : q y
        · have hxy' := hxy
          simp only [threeWayMap, dif_pos hpx, dif_pos hpy,
            dif_neg hqx, dif_pos hqy] at hxy'
          cases hxy'
        · have hbranch : second ⟨x, hpx, hqx⟩ = second ⟨y, hpy, hqy⟩ := by
            simpa [threeWayMap, hpx, hpy, hqx, hqy] using hxy
          exact congrArg Subtype.val (hsecond hbranch)
    · have hxy' := hxy
      have htag := congrArg
        (fun z : Sum β (Sum γ δ) => match z with
          | Sum.inl _ => true
          | Sum.inr _ => false) hxy'
      by_cases hqx : q x <;> simp [threeWayMap, hpx, hpy, hqx] at htag
  · by_cases hpy : p y
    · have hxy' := hxy
      have htag := congrArg
        (fun z : Sum β (Sum γ δ) => match z with
          | Sum.inl _ => true
          | Sum.inr _ => false) hxy'
      by_cases hqy : q y <;> simp [threeWayMap, hpx, hpy, hqy] at htag
    · have hbranch : first ⟨x, hpx⟩ = first ⟨y, hpy⟩ := by
        simpa [threeWayMap, hpx, hpy] using hxy
      exact congrArg Subtype.val (hfirst hbranch)

/-! ## `X`: delete one lower cell, or delete the lower domino -/

private def xNorth {n : ℕ} (x : MarkedOccurrence BuiNeighborhood.x n) : Prop :=
  cellAt x.2.1 0 1 ∈ x.1.toPolyomino.cells

private def xNortheast {n : ℕ}
    (x : MarkedOccurrence BuiNeighborhood.x n) : Prop :=
  cellAt x.2.1 1 1 ∈ x.1.toPolyomino.cells

private theorem xFrame {n : ℕ} (x : MarkedOccurrence BuiNeighborhood.x n) :
    DominoFrame x.1.toPolyomino.cells x.2.1 :=
  x_occursAt_frame (marked_occursAt x)

private def xFirstPack {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.x n // ¬xNorth x}) :
    LeafDeletionOccurrence n westOffset :=
  deleteLeftLeaf x.1.1 x.1.2.1 (xFrame x.1) x.2

private theorem xFirstPack_injective {n : ℕ} :
    Function.Injective (xFirstPack (n := n)) := by
  intro x y hxy
  apply Subtype.ext
  apply markedOccurrence_ext
  · exact congrArg LeafDeletionOccurrence.polyomino hxy
  · have hp := congrArg LeafDeletionOccurrence.parent hxy
    change x.1.2.1 + ((1, 0) : Cell) =
      y.1.2.1 + ((1, 0) : Cell) at hp
    exact add_right_cancel hp

private theorem xFirstRaw {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.x n // ¬xNorth x}) :
    buiDPattern.OccursAt (xFirstPack x).erased.cells
      (xFirstPack x).parent := by
  exact x_delete_left_occursAt_d (marked_occursAt x.1) x.2

private noncomputable def xFirstMap {n : ℕ} :
    {x : MarkedOccurrence BuiNeighborhood.x n // ¬xNorth x} →
      MarkedOccurrence BuiNeighborhood.d (n - 1) :=
  markedAfterLeaf xFirstPack xFirstRaw

private theorem xFirstMap_injective {n : ℕ} :
    Function.Injective (xFirstMap (n := n)) :=
  markedAfterLeaf_injective xFirstPack xFirstPack_injective xFirstRaw

private def xSecondPack {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.x n //
      xNorth x ∧ ¬xNortheast x}) :
    PairDeletionOccurrence n southeastOffset southOffset :=
  deletePairMarkLeftUpper x.1.1 x.1.2.1 (xFrame x.1) x.2.1
    (connected_delete_right_then_left (xFrame x.1) x.2.1 x.2.2)

private theorem xSecondPack_injective {n : ℕ} :
    Function.Injective (xSecondPack (n := n)) := by
  intro x y hxy
  apply Subtype.ext
  apply markedOccurrence_ext
  · exact congrArg PairDeletionOccurrence.polyomino hxy
  · have hm := congrArg PairDeletionOccurrence.mark hxy
    change x.1.2.1 + ((0, 1) : Cell) =
      y.1.2.1 + ((0, 1) : Cell) at hm
    exact add_right_cancel hm

private theorem xSecondRaw {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.x n //
      xNorth x ∧ ¬xNortheast x}) :
    rightGPattern.OccursAt (xSecondPack x).erased.cells
      (xSecondPack x).mark :=
  by
    change rightGPattern.OccursAt
      ((x.1.1.toPolyomino.cells.erase
        (cellAt x.1.2.1 0 1 + southeastOffset)).erase
        (cellAt x.1.2.1 0 1 + southOffset))
      (cellAt x.1.2.1 0 1)
    rw [leftUpper_add_southeast, leftUpper_add_south]
    exact x_delete_pair_left_only_occursAt_rightG
      (marked_occursAt x.1) x.2.1 x.2.2

private theorem xSecondNormalizedRaw {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.x n //
      xNorth x ∧ ¬xNortheast x}) :
    rightGPattern.OccursAt
      (xSecondPack x).normalizedRemainder.toPolyomino.cells
      ((xSecondPack x).normalizationVector + (xSecondPack x).mark) := by
  exact (xSecondRaw x).translate (xSecondPack x).normalizationVector

private noncomputable def xSecondMap {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.x n //
      xNorth x ∧ ¬xNortheast x}) :
    MarkedOccurrence BuiNeighborhood.g (n - 2) :=
  mirrorMarkedG (xSecondPack x).normalizedRemainder
    ((xSecondPack x).normalizationVector + (xSecondPack x).mark)
    (xSecondNormalizedRaw x)

private theorem xSecondMap_injective {n : ℕ} :
    Function.Injective (xSecondMap (n := n)) := by
  intro x y hxy
  have hdata := mirrorMarkedG_injective_on_data hxy
  have hdelete : (xSecondPack x).deleteData = (xSecondPack y).deleteData := by
    exact Prod.ext hdata.1 hdata.2
  exact xSecondPack_injective
    (PairDeletionOccurrence.deleteData_injective n southeastOffset southOffset
      hdelete)

private def xThirdPack {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.x n //
      xNorth x ∧ xNortheast x}) :
    PairDeletionOccurrence n southeastOffset southOffset :=
  deletePairMarkLeftUpper x.1.1 x.1.2.1 (xFrame x.1) x.2.1
    (connected_delete_both_with_upper_bridge (xFrame x.1) x.2.1 x.2.2)

private theorem xThirdPack_injective {n : ℕ} :
    Function.Injective (xThirdPack (n := n)) := by
  intro x y hxy
  apply Subtype.ext
  apply markedOccurrence_ext
  · exact congrArg PairDeletionOccurrence.polyomino hxy
  · have hm := congrArg PairDeletionOccurrence.mark hxy
    change x.1.2.1 + ((0, 1) : Cell) =
      y.1.2.1 + ((0, 1) : Cell) at hm
    exact add_right_cancel hm

private theorem xThirdRaw {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.x n //
      xNorth x ∧ xNortheast x}) :
    buiUPattern.OccursAt (xThirdPack x).erased.cells
      (xThirdPack x).mark :=
  by
    change buiUPattern.OccursAt
      ((x.1.1.toPolyomino.cells.erase
        (cellAt x.1.2.1 0 1 + southeastOffset)).erase
        (cellAt x.1.2.1 0 1 + southOffset))
      (cellAt x.1.2.1 0 1)
    rw [leftUpper_add_southeast, leftUpper_add_south]
    exact x_delete_pair_both_occursAt_u
      (marked_occursAt x.1) x.2.1 x.2.2

private noncomputable def xThirdMap {n : ℕ} :
    {x : MarkedOccurrence BuiNeighborhood.x n //
      xNorth x ∧ xNortheast x} →
      MarkedOccurrence BuiNeighborhood.u (n - 2) :=
  markedAfterPair xThirdPack xThirdRaw

private theorem xThirdMap_injective {n : ℕ} :
    Function.Injective (xThirdMap (n := n)) :=
  markedAfterPair_injective xThirdPack xThirdPack_injective xThirdRaw

private noncomputable def xThreeWayMap (n : ℕ) :
    MarkedOccurrence BuiNeighborhood.x n →
      MarkedOccurrence BuiNeighborhood.d (n - 1) ⊕
        (MarkedOccurrence BuiNeighborhood.g (n - 2) ⊕
          MarkedOccurrence BuiNeighborhood.u (n - 2)) := by
  classical
  exact threeWayMap xNorth xNortheast xFirstMap xSecondMap xThirdMap

private theorem xThreeWayMap_injective (n : ℕ) :
    Function.Injective (xThreeWayMap n) := by
  classical
  exact threeWayMap_injective xNorth xNortheast
    xFirstMap xSecondMap xThirdMap
    xFirstMap_injective xSecondMap_injective xThirdMap_injective

/-- The aggregate marked-occurrence form of Bui's `X` recurrence. -/
theorem buiX_aggregateOccurrenceCount_le_d_add_g_add_u (n : ℕ) :
    BuiNeighborhood.x.aggregateOccurrenceCount n ≤
      BuiNeighborhood.d.aggregateOccurrenceCount (n - 1) +
        BuiNeighborhood.g.aggregateOccurrenceCount (n - 2) +
          BuiNeighborhood.u.aggregateOccurrenceCount (n - 2) := by
  rw [← card_markedOccurrence, ← card_markedOccurrence,
    ← card_markedOccurrence, ← card_markedOccurrence]
  simpa [Fintype.card_sum, Nat.add_assoc] using
    Fintype.card_le_of_injective (xThreeWayMap n) (xThreeWayMap_injective n)

/-- The coefficient form used by `PublishedBuiRecurrences`. -/
theorem buiX_coefficient_le_d_add_g_add_u (n : ℕ) :
    BuiNeighborhood.x.coefficient n ≤
      BuiNeighborhood.d.coefficient (n - 1) +
        BuiNeighborhood.g.coefficient (n - 2) +
          BuiNeighborhood.u.coefficient (n - 2) := by
  change (BuiNeighborhood.x.aggregateOccurrenceCount n : ℚ) ≤
    (BuiNeighborhood.d.aggregateOccurrenceCount (n - 1) : ℚ) +
      (BuiNeighborhood.g.aggregateOccurrenceCount (n - 2) : ℚ) +
        (BuiNeighborhood.u.aggregateOccurrenceCount (n - 2) : ℚ)
  exact_mod_cast buiX_aggregateOccurrenceCount_le_d_add_g_add_u n

/-! ## `Y`: split first by the upper-right cell -/

private def yNorth {n : ℕ} (x : MarkedOccurrence BuiNeighborhood.y n) : Prop :=
  cellAt x.2.1 0 1 ∈ x.1.toPolyomino.cells

private def yNortheast {n : ℕ}
    (x : MarkedOccurrence BuiNeighborhood.y n) : Prop :=
  cellAt x.2.1 1 1 ∈ x.1.toPolyomino.cells

private theorem yFrame {n : ℕ} (x : MarkedOccurrence BuiNeighborhood.y n) :
    DominoFrame x.1.toPolyomino.cells x.2.1 :=
  y_occursAt_frame (marked_occursAt x)

private def yFirstPack {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.y n // ¬yNortheast x}) :
    LeafDeletionOccurrence n eastOffset :=
  deleteRightLeaf x.1.1 x.1.2.1 (yFrame x.1) x.2

private theorem yFirstPack_injective {n : ℕ} :
    Function.Injective (yFirstPack (n := n)) := by
  intro x y hxy
  apply Subtype.ext
  apply markedOccurrence_ext
  · exact congrArg LeafDeletionOccurrence.polyomino hxy
  · exact congrArg LeafDeletionOccurrence.parent hxy

private theorem yFirstRaw {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.y n // ¬yNortheast x}) :
    buiCPattern.OccursAt (yFirstPack x).erased.cells
      (yFirstPack x).parent :=
  y_delete_right_occursAt_c (marked_occursAt x.1) x.2

private noncomputable def yFirstMap {n : ℕ} :
    {x : MarkedOccurrence BuiNeighborhood.y n // ¬yNortheast x} →
      MarkedOccurrence BuiNeighborhood.c (n - 1) :=
  markedAfterLeaf yFirstPack yFirstRaw

private theorem yFirstMap_injective {n : ℕ} :
    Function.Injective (yFirstMap (n := n)) :=
  markedAfterLeaf_injective yFirstPack yFirstPack_injective yFirstRaw

private def ySecondPack {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.y n //
      yNortheast x ∧ ¬yNorth x}) :
    PairDeletionOccurrence n southwestOffset southOffset :=
  deletePairMarkRightUpper x.1.1 x.1.2.1 (yFrame x.1) x.2.1
    (connected_delete_left_then_right (yFrame x.1) x.2.2 x.2.1)

private theorem ySecondPack_injective {n : ℕ} :
    Function.Injective (ySecondPack (n := n)) := by
  intro x y hxy
  apply Subtype.ext
  apply markedOccurrence_ext
  · exact congrArg PairDeletionOccurrence.polyomino hxy
  · have hm := congrArg PairDeletionOccurrence.mark hxy
    change x.1.2.1 + ((1, 1) : Cell) =
      y.1.2.1 + ((1, 1) : Cell) at hm
    exact add_right_cancel hm

private theorem ySecondRaw {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.y n //
      yNortheast x ∧ ¬yNorth x}) :
    buiGPattern.OccursAt (ySecondPack x).erased.cells
      (ySecondPack x).mark :=
  by
    change buiGPattern.OccursAt
      ((x.1.1.toPolyomino.cells.erase
        (cellAt x.1.2.1 1 1 + southwestOffset)).erase
        (cellAt x.1.2.1 1 1 + southOffset))
      (cellAt x.1.2.1 1 1)
    rw [rightUpper_add_southwest, rightUpper_add_south]
    exact y_delete_pair_right_only_occursAt_g
      (marked_occursAt x.1) x.2.2 x.2.1

private noncomputable def ySecondMap {n : ℕ} :
    {x : MarkedOccurrence BuiNeighborhood.y n //
      yNortheast x ∧ ¬yNorth x} →
      MarkedOccurrence BuiNeighborhood.g (n - 2) :=
  markedAfterPair ySecondPack ySecondRaw

private theorem ySecondMap_injective {n : ℕ} :
    Function.Injective (ySecondMap (n := n)) :=
  markedAfterPair_injective ySecondPack ySecondPack_injective ySecondRaw

private def yThirdPack {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.y n //
      yNortheast x ∧ yNorth x}) :
    PairDeletionOccurrence n southeastOffset southOffset :=
  deletePairMarkLeftUpper x.1.1 x.1.2.1 (yFrame x.1) x.2.2
    (connected_delete_both_with_upper_bridge (yFrame x.1) x.2.2 x.2.1)

private theorem yThirdPack_injective {n : ℕ} :
    Function.Injective (yThirdPack (n := n)) := by
  intro x y hxy
  apply Subtype.ext
  apply markedOccurrence_ext
  · exact congrArg PairDeletionOccurrence.polyomino hxy
  · have hm := congrArg PairDeletionOccurrence.mark hxy
    change x.1.2.1 + ((0, 1) : Cell) =
      y.1.2.1 + ((0, 1) : Cell) at hm
    exact add_right_cancel hm

private theorem yThirdRaw {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.y n //
      yNortheast x ∧ yNorth x}) :
    buiTPattern.OccursAt (yThirdPack x).erased.cells
      (yThirdPack x).mark :=
  by
    change buiTPattern.OccursAt
      ((x.1.1.toPolyomino.cells.erase
        (cellAt x.1.2.1 0 1 + southeastOffset)).erase
        (cellAt x.1.2.1 0 1 + southOffset))
      (cellAt x.1.2.1 0 1)
    rw [leftUpper_add_southeast, leftUpper_add_south]
    exact y_delete_pair_both_occursAt_t
      (marked_occursAt x.1) x.2.2 x.2.1

private noncomputable def yThirdMap {n : ℕ} :
    {x : MarkedOccurrence BuiNeighborhood.y n //
      yNortheast x ∧ yNorth x} →
      MarkedOccurrence BuiNeighborhood.t (n - 2) :=
  markedAfterPair yThirdPack yThirdRaw

private theorem yThirdMap_injective {n : ℕ} :
    Function.Injective (yThirdMap (n := n)) :=
  markedAfterPair_injective yThirdPack yThirdPack_injective yThirdRaw

private noncomputable def yThreeWayMap (n : ℕ) :
    MarkedOccurrence BuiNeighborhood.y n →
      MarkedOccurrence BuiNeighborhood.c (n - 1) ⊕
        (MarkedOccurrence BuiNeighborhood.g (n - 2) ⊕
          MarkedOccurrence BuiNeighborhood.t (n - 2)) := by
  classical
  exact threeWayMap yNortheast yNorth yFirstMap ySecondMap yThirdMap

private theorem yThreeWayMap_injective (n : ℕ) :
    Function.Injective (yThreeWayMap n) := by
  classical
  exact threeWayMap_injective yNortheast yNorth
    yFirstMap ySecondMap yThirdMap
    yFirstMap_injective ySecondMap_injective yThirdMap_injective

/-- The aggregate marked-occurrence form of Bui's `Y` recurrence. -/
theorem buiY_aggregateOccurrenceCount_le_c_add_g_add_t (n : ℕ) :
    BuiNeighborhood.y.aggregateOccurrenceCount n ≤
      BuiNeighborhood.c.aggregateOccurrenceCount (n - 1) +
        BuiNeighborhood.g.aggregateOccurrenceCount (n - 2) +
          BuiNeighborhood.t.aggregateOccurrenceCount (n - 2) := by
  rw [← card_markedOccurrence, ← card_markedOccurrence,
    ← card_markedOccurrence, ← card_markedOccurrence]
  simpa [Fintype.card_sum, Nat.add_assoc] using
    Fintype.card_le_of_injective (yThreeWayMap n) (yThreeWayMap_injective n)

/-- The coefficient form used by `PublishedBuiRecurrences`. -/
theorem buiY_coefficient_le_c_add_g_add_t (n : ℕ) :
    BuiNeighborhood.y.coefficient n ≤
      BuiNeighborhood.c.coefficient (n - 1) +
        BuiNeighborhood.g.coefficient (n - 2) +
          BuiNeighborhood.t.coefficient (n - 2) := by
  change (BuiNeighborhood.y.aggregateOccurrenceCount n : ℚ) ≤
    (BuiNeighborhood.c.aggregateOccurrenceCount (n - 1) : ℚ) +
      (BuiNeighborhood.g.aggregateOccurrenceCount (n - 2) : ℚ) +
        (BuiNeighborhood.t.aggregateOccurrenceCount (n - 2) : ℚ)
  exact_mod_cast buiY_aggregateOccurrenceCount_le_c_add_g_add_t n

/-! ## `Z`: split first by the upper-left cell -/

private def zNorth {n : ℕ} (x : MarkedOccurrence BuiNeighborhood.z n) : Prop :=
  cellAt x.2.1 0 1 ∈ x.1.toPolyomino.cells

private def zNortheast {n : ℕ}
    (x : MarkedOccurrence BuiNeighborhood.z n) : Prop :=
  cellAt x.2.1 1 1 ∈ x.1.toPolyomino.cells

private theorem zFrame {n : ℕ} (x : MarkedOccurrence BuiNeighborhood.z n) :
    DominoFrame x.1.toPolyomino.cells x.2.1 :=
  z_occursAt_frame (marked_occursAt x)

private def zFirstPack {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.z n // ¬zNorth x}) :
    LeafDeletionOccurrence n westOffset :=
  deleteLeftLeaf x.1.1 x.1.2.1 (zFrame x.1) x.2

private theorem zFirstPack_injective {n : ℕ} :
    Function.Injective (zFirstPack (n := n)) := by
  intro x y hxy
  apply Subtype.ext
  apply markedOccurrence_ext
  · exact congrArg LeafDeletionOccurrence.polyomino hxy
  · have hp := congrArg LeafDeletionOccurrence.parent hxy
    change x.1.2.1 + ((1, 0) : Cell) =
      y.1.2.1 + ((1, 0) : Cell) at hp
    exact add_right_cancel hp

private theorem zFirstRaw {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.z n // ¬zNorth x}) :
    buiCPattern.OccursAt (zFirstPack x).erased.cells
      (zFirstPack x).parent :=
  z_delete_left_occursAt_c (marked_occursAt x.1) x.2

private noncomputable def zFirstMap {n : ℕ} :
    {x : MarkedOccurrence BuiNeighborhood.z n // ¬zNorth x} →
      MarkedOccurrence BuiNeighborhood.c (n - 1) :=
  markedAfterLeaf zFirstPack zFirstRaw

private theorem zFirstMap_injective {n : ℕ} :
    Function.Injective (zFirstMap (n := n)) :=
  markedAfterLeaf_injective zFirstPack zFirstPack_injective zFirstRaw

private def zSecondPack {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.z n //
      zNorth x ∧ ¬zNortheast x}) :
    PairDeletionOccurrence n southeastOffset southOffset :=
  deletePairMarkLeftUpper x.1.1 x.1.2.1 (zFrame x.1) x.2.1
    (connected_delete_right_then_left (zFrame x.1) x.2.1 x.2.2)

private theorem zSecondPack_injective {n : ℕ} :
    Function.Injective (zSecondPack (n := n)) := by
  intro x y hxy
  apply Subtype.ext
  apply markedOccurrence_ext
  · exact congrArg PairDeletionOccurrence.polyomino hxy
  · have hm := congrArg PairDeletionOccurrence.mark hxy
    change x.1.2.1 + ((0, 1) : Cell) =
      y.1.2.1 + ((0, 1) : Cell) at hm
    exact add_right_cancel hm

private theorem zSecondRaw {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.z n //
      zNorth x ∧ ¬zNortheast x}) :
    buiEPattern.OccursAt (zSecondPack x).erased.cells
      (zSecondPack x).mark :=
  by
    change buiEPattern.OccursAt
      ((x.1.1.toPolyomino.cells.erase
        (cellAt x.1.2.1 0 1 + southeastOffset)).erase
        (cellAt x.1.2.1 0 1 + southOffset))
      (cellAt x.1.2.1 0 1)
    rw [leftUpper_add_southeast, leftUpper_add_south]
    exact z_delete_pair_left_only_occursAt_e
      (marked_occursAt x.1) x.2.1 x.2.2

private noncomputable def zSecondMap {n : ℕ} :
    {x : MarkedOccurrence BuiNeighborhood.z n //
      zNorth x ∧ ¬zNortheast x} →
      MarkedOccurrence BuiNeighborhood.e (n - 2) :=
  markedAfterPair zSecondPack zSecondRaw

private theorem zSecondMap_injective {n : ℕ} :
    Function.Injective (zSecondMap (n := n)) :=
  markedAfterPair_injective zSecondPack zSecondPack_injective zSecondRaw

private def zThirdPack {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.z n //
      zNorth x ∧ zNortheast x}) :
    PairDeletionOccurrence n southeastOffset southOffset :=
  deletePairMarkLeftUpper x.1.1 x.1.2.1 (zFrame x.1) x.2.1
    (connected_delete_both_with_upper_bridge (zFrame x.1) x.2.1 x.2.2)

private theorem zThirdPack_injective {n : ℕ} :
    Function.Injective (zThirdPack (n := n)) := by
  intro x y hxy
  apply Subtype.ext
  apply markedOccurrence_ext
  · exact congrArg PairDeletionOccurrence.polyomino hxy
  · have hm := congrArg PairDeletionOccurrence.mark hxy
    change x.1.2.1 + ((0, 1) : Cell) =
      y.1.2.1 + ((0, 1) : Cell) at hm
    exact add_right_cancel hm

private theorem zThirdRaw {n : ℕ}
    (x : {x : MarkedOccurrence BuiNeighborhood.z n //
      zNorth x ∧ zNortheast x}) :
    buiXPattern.OccursAt (zThirdPack x).erased.cells
      (zThirdPack x).mark :=
  by
    change buiXPattern.OccursAt
      ((x.1.1.toPolyomino.cells.erase
        (cellAt x.1.2.1 0 1 + southeastOffset)).erase
        (cellAt x.1.2.1 0 1 + southOffset))
      (cellAt x.1.2.1 0 1)
    rw [leftUpper_add_southeast, leftUpper_add_south]
    exact z_delete_pair_both_occursAt_x
      (marked_occursAt x.1) x.2.1 x.2.2

private noncomputable def zThirdMap {n : ℕ} :
    {x : MarkedOccurrence BuiNeighborhood.z n //
      zNorth x ∧ zNortheast x} →
      MarkedOccurrence BuiNeighborhood.x (n - 2) :=
  markedAfterPair zThirdPack zThirdRaw

private theorem zThirdMap_injective {n : ℕ} :
    Function.Injective (zThirdMap (n := n)) :=
  markedAfterPair_injective zThirdPack zThirdPack_injective zThirdRaw

private noncomputable def zThreeWayMap (n : ℕ) :
    MarkedOccurrence BuiNeighborhood.z n →
      MarkedOccurrence BuiNeighborhood.c (n - 1) ⊕
        (MarkedOccurrence BuiNeighborhood.e (n - 2) ⊕
          MarkedOccurrence BuiNeighborhood.x (n - 2)) := by
  classical
  exact threeWayMap zNorth zNortheast zFirstMap zSecondMap zThirdMap

private theorem zThreeWayMap_injective (n : ℕ) :
    Function.Injective (zThreeWayMap n) := by
  classical
  exact threeWayMap_injective zNorth zNortheast
    zFirstMap zSecondMap zThirdMap
    zFirstMap_injective zSecondMap_injective zThirdMap_injective

/-- The aggregate marked-occurrence form of Bui's `Z` recurrence. -/
theorem buiZ_aggregateOccurrenceCount_le_c_add_e_add_x (n : ℕ) :
    BuiNeighborhood.z.aggregateOccurrenceCount n ≤
      BuiNeighborhood.c.aggregateOccurrenceCount (n - 1) +
        BuiNeighborhood.e.aggregateOccurrenceCount (n - 2) +
          BuiNeighborhood.x.aggregateOccurrenceCount (n - 2) := by
  rw [← card_markedOccurrence, ← card_markedOccurrence,
    ← card_markedOccurrence, ← card_markedOccurrence]
  simpa [Fintype.card_sum, Nat.add_assoc] using
    Fintype.card_le_of_injective (zThreeWayMap n) (zThreeWayMap_injective n)

/-- The coefficient form used by `PublishedBuiRecurrences`. -/
theorem buiZ_coefficient_le_c_add_e_add_x (n : ℕ) :
    BuiNeighborhood.z.coefficient n ≤
      BuiNeighborhood.c.coefficient (n - 1) +
        BuiNeighborhood.e.coefficient (n - 2) +
          BuiNeighborhood.x.coefficient (n - 2) := by
  change (BuiNeighborhood.z.aggregateOccurrenceCount n : ℚ) ≤
    (BuiNeighborhood.c.aggregateOccurrenceCount (n - 1) : ℚ) +
      (BuiNeighborhood.e.aggregateOccurrenceCount (n - 2) : ℚ) +
        (BuiNeighborhood.x.aggregateOccurrenceCount (n - 2) : ℚ)
  exact_mod_cast buiZ_aggregateOccurrenceCount_le_c_add_e_add_x n

end LeanProofs.KlarnerConstant
