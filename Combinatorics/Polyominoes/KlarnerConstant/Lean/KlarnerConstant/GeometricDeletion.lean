import KlarnerConstant.GeometricLinear
import Mathlib.Data.Fintype.BigOperators
import KlarnerConstant.TranslationClasses

/-!
# The three one-cell deletion inequalities in Bui's system

This module proves the geometric part of

* `C(n) <= E(n - 1)`,
* `D(n) <= G(n - 1)`, and
* `E(n) <= F(n - 1)`

for `2 <= n`.  Together with the separately verified one-cell initial value,
these are the three inequalities usually written with an additional
Kronecker delta at `n = 1`.

The common construction is completely explicit.  A `C`, `D`, or `E` anchor
has no occupied neighbor to its west, east, or south.  In a polyomino with at
least two cells, connectedness therefore forces its north neighbor to be
occupied.  The anchor is a leaf of the grid adjacency graph.  We delete it,
normalize the remaining polyomino, and mark the translated north neighbor.
The local forbidden-cell diagrams turn this into respectively an `E`, `G`,
or `F` occurrence.

The map on marked occurrences is injective.  From the normalized remainder
and its marked cell one reconstructs the translated original cell set by
inserting the cell immediately south of the mark.  Normalization then recovers
the original normalized polyomino, and its southwest anchor recovers the
translation vector.  Thus the original marked anchor is recovered as well.
-/

namespace LeanProofs.KlarnerConstant

private def northOffset : Cell := (0, 1)
private def southOffset : Cell := (0, -1)
private def westOffset : Cell := (-1, 0)
private def eastOffset : Cell := (1, 0)

private theorem add_north_ne_self (anchor : Cell) :
    anchor + northOffset ≠ anchor := by
  intro h
  have h' := congrArg Prod.snd h
  norm_num [northOffset] at h'

private theorem add_north_add_south (anchor : Cell) :
    (anchor + northOffset) + southOffset = anchor := by
  apply Prod.ext <;> norm_num [northOffset, southOffset]

private theorem add_north_add_west (anchor : Cell) :
    (anchor + northOffset) + westOffset = anchor + (-1, 1) := by
  apply Prod.ext <;> norm_num [northOffset, westOffset]

private theorem add_north_add_east (anchor : Cell) :
    (anchor + northOffset) + eastOffset = anchor + (1, 1) := by
  apply Prod.ext <;> norm_num [northOffset, eastOffset]

private theorem add_north_add_southwest (anchor : Cell) :
    (anchor + northOffset) + (-1, -1) = anchor + westOffset := by
  apply Prod.ext <;> norm_num [northOffset, westOffset]

private theorem add_north_add_southeast (anchor : Cell) :
    (anchor + northOffset) + (1, -1) = anchor + eastOffset := by
  apply Prod.ext <;> norm_num [northOffset, eastOffset]

private theorem add_zero_offset (anchor : Cell) :
    anchor + (0, 0) = anchor := by
  apply Prod.ext <;> simp

/-! ## Deleting a north-attached leaf -/

/-- The data saying that `anchor` is an occupied leaf whose unique possible
grid neighbor is the occupied cell immediately north of it. -/
structure NorthLeafAt (cells : Finset Cell) (anchor : Cell) : Prop where
  anchor_mem : anchor ∈ cells
  north_mem : anchor + northOffset ∈ cells
  west_not_mem : anchor + westOffset ∉ cells
  east_not_mem : anchor + eastOffset ∉ cells
  south_not_mem : anchor + southOffset ∉ cells

/-- If the three other grid neighbors of `anchor` are absent, every occupied
cell adjacent to it is its north neighbor. -/
private theorem adjacent_mem_eq_north {cells : Finset Cell} {anchor other : Cell}
    (hwest : anchor + westOffset ∉ cells)
    (heast : anchor + eastOffset ∉ cells)
    (hsouth : anchor + southOffset ∉ cells)
    (hother : other ∈ cells) (hadjacent : EdgeAdjacent anchor other) :
    other = anchor + northOffset := by
  rcases hadjacent with h | h | h | h <;> subst other
  · exfalso
    apply heast
    have hcoordinate : anchor + eastOffset = (anchor.1 + 1, anchor.2) := by
      apply Prod.ext <;> simp [eastOffset]
    rwa [hcoordinate]
  · exfalso
    apply hwest
    have hcoordinate : anchor + westOffset = (anchor.1 - 1, anchor.2) := by
      apply Prod.ext <;> simp [westOffset, sub_eq_add_neg]
    rwa [hcoordinate]
  · apply Prod.ext <;> norm_num [northOffset]
  · exfalso
    apply hsouth
    have hcoordinate : anchor + southOffset = (anchor.1, anchor.2 - 1) := by
      apply Prod.ext <;> simp [southOffset, sub_eq_add_neg]
    rwa [hcoordinate]

/-- In a connected cell set of cardinality at least two, the only possible
neighbor of such an anchor really is present. -/
private theorem north_mem_of_connected {P : Polyomino} {anchor : Cell}
    (hanchor : anchor ∈ P.cells)
    (hwest : anchor + westOffset ∉ P.cells)
    (heast : anchor + eastOffset ∉ P.cells)
    (hsouth : anchor + southOffset ∉ P.cells)
    (hcard : 2 ≤ P.cells.card) :
    anchor + northOffset ∈ P.cells := by
  classical
  by_contra hnorth
  have reachable_eq_anchor : ∀ {other : Cell},
      Relation.ReflTransGen (EdgeAdjacentIn P.cells) anchor other →
        other = anchor := by
    intro other hpath
    induction hpath with
    | refl => rfl
    | @tail middle last hprefix hstep ih =>
        subst middle
        have hlast : last = anchor + northOffset :=
          adjacent_mem_eq_north hwest heast hsouth hstep.2.1 hstep.2.2
        subst last
        exact False.elim (hnorth hstep.2.1)
  have hunique : ∀ other ∈ P.cells, other = anchor := by
    intro other hother
    exact reachable_eq_anchor (P.edgeConnected anchor hanchor other hother)
  have hsubset : P.cells ⊆ {anchor} := by
    intro other hother
    simpa only [Finset.mem_singleton] using hunique other hother
  have hone : P.cells.card ≤ 1 := by
    calc
      P.cells.card ≤ ({anchor} : Finset Cell).card :=
        Finset.card_le_card hsubset
      _ = 1 := by simp
  omega

/-- A local pattern which forbids west, east, and south at its anchor makes
that anchor a north-attached leaf in every non-singleton polyomino. -/
private theorem northLeafAt_of_three_forbidden {P : Polyomino} {anchor : Cell}
    (hanchor : anchor ∈ P.cells)
    (hwest : anchor + westOffset ∉ P.cells)
    (heast : anchor + eastOffset ∉ P.cells)
    (hsouth : anchor + southOffset ∉ P.cells)
    (hcard : 2 ≤ P.cells.card) :
    NorthLeafAt P.cells anchor := by
  exact ⟨hanchor,
    north_mem_of_connected hanchor hwest heast hsouth hcard,
    hwest, heast, hsouth⟩

private def retractNorth (anchor other : Cell) : Cell :=
  if other = anchor then anchor + northOffset else other

private theorem edge_step_survives_erase {P : Polyomino} {anchor x y : Cell}
    (hleaf : NorthLeafAt P.cells anchor)
    (hxy : EdgeAdjacentIn P.cells x y) :
    Relation.ReflTransGen (EdgeAdjacentIn (P.cells.erase anchor))
      (retractNorth anchor x) (retractNorth anchor y) := by
  by_cases hx : x = anchor
  · subst x
    have hy : y = anchor + northOffset :=
      adjacent_mem_eq_north hleaf.west_not_mem hleaf.east_not_mem
        hleaf.south_not_mem hxy.2.1 hxy.2.2
    subst y
    simpa [retractNorth, add_north_ne_self] using
      (Relation.ReflTransGen.refl :
        Relation.ReflTransGen (EdgeAdjacentIn (P.cells.erase anchor))
          (anchor + northOffset) (anchor + northOffset))
  · by_cases hy : y = anchor
    · subst y
      have hxparent : x = anchor + northOffset :=
        adjacent_mem_eq_north hleaf.west_not_mem hleaf.east_not_mem
          hleaf.south_not_mem hxy.1 (edgeAdjacent_symm hxy.2.2)
      subst x
      simpa [retractNorth, add_north_ne_self] using
        (Relation.ReflTransGen.refl :
          Relation.ReflTransGen (EdgeAdjacentIn (P.cells.erase anchor))
            (anchor + northOffset) (anchor + northOffset))
    · apply Relation.ReflTransGen.single
      simpa [retractNorth, hx, hy] using
        (show EdgeAdjacentIn (P.cells.erase anchor) x y from
          ⟨Finset.mem_erase.mpr ⟨hx, hxy.1⟩,
            Finset.mem_erase.mpr ⟨hy, hxy.2.1⟩, hxy.2.2⟩)

private theorem edgeConnected_erase_northLeaf {P : Polyomino} {anchor : Cell}
    (hleaf : NorthLeafAt P.cells anchor) :
    EdgeConnected (P.cells.erase anchor) := by
  intro x hx y hy
  have hx' := Finset.mem_erase.mp hx
  have hy' := Finset.mem_erase.mp hy
  have hpath := P.edgeConnected x hx'.2 y hy'.2
  have hlift := hpath.lift' (retractNorth anchor)
    (fun _ _ hstep => edge_step_survives_erase hleaf hstep)
  have hxfix : retractNorth anchor x = x := by
    simp [retractNorth, hx'.1]
  have hyfix : retractNorth anchor y = y := by
    simp [retractNorth, hy'.1]
  change Relation.ReflTransGen (EdgeAdjacentIn (P.cells.erase anchor))
    (retractNorth anchor x) (retractNorth anchor y) at hlift
  simpa only [hxfix, hyfix] using hlift

/-- Delete a north-attached leaf from a polyomino. -/
def Polyomino.eraseNorthLeaf (P : Polyomino) (anchor : Cell)
    (hleaf : NorthLeafAt P.cells anchor) : Polyomino where
  cells := P.cells.erase anchor
  nonempty := by
    refine ⟨anchor + northOffset, Finset.mem_erase.mpr ⟨?_, hleaf.north_mem⟩⟩
    exact add_north_ne_self anchor
  edgeConnected := edgeConnected_erase_northLeaf hleaf

@[simp]
theorem Polyomino.cells_eraseNorthLeaf (P : Polyomino) (anchor : Cell)
    (hleaf : NorthLeafAt P.cells anchor) :
    (P.eraseNorthLeaf anchor hleaf).cells = P.cells.erase anchor :=
  rfl

@[simp]
theorem Polyomino.card_cells_eraseNorthLeaf (P : Polyomino) (anchor : Cell)
    (hleaf : NorthLeafAt P.cells anchor) :
    (P.eraseNorthLeaf anchor hleaf).cells.card = P.cells.card - 1 := by
  exact Finset.card_erase_of_mem hleaf.anchor_mem

/-! ## Local transformations of the three patterns -/

private theorem c_occursAt_northLeaf {P : Polyomino} {anchor : Cell}
    (hoccurs : buiCPattern.OccursAt P.cells anchor)
    (hcard : 2 ≤ P.cells.card) : NorthLeafAt P.cells anchor := by
  have hanchor : anchor ∈ P.cells := by
    have hrequired := hoccurs.1 (0, 0) (by simp [buiCPattern])
    rw [add_zero_offset] at hrequired
    exact hrequired
  have hwest : anchor + westOffset ∉ P.cells :=
    hoccurs.2 westOffset (by simp [buiCPattern, westOffset])
  have heast : anchor + eastOffset ∉ P.cells :=
    hoccurs.2 eastOffset (by simp [buiCPattern, eastOffset])
  have hsouth : anchor + southOffset ∉ P.cells :=
    hoccurs.2 southOffset (by simp [buiCPattern, southOffset])
  exact northLeafAt_of_three_forbidden hanchor hwest heast hsouth hcard

private theorem d_occursAt_northLeaf {P : Polyomino} {anchor : Cell}
    (hoccurs : buiDPattern.OccursAt P.cells anchor)
    (hcard : 2 ≤ P.cells.card) : NorthLeafAt P.cells anchor := by
  have hanchor : anchor ∈ P.cells := by
    have hrequired := hoccurs.1 (0, 0) (by simp [buiDPattern])
    rw [add_zero_offset] at hrequired
    exact hrequired
  have hwest : anchor + westOffset ∉ P.cells :=
    hoccurs.2 westOffset (by simp [buiDPattern, westOffset])
  have heast : anchor + eastOffset ∉ P.cells :=
    hoccurs.2 eastOffset (by simp [buiDPattern, eastOffset])
  have hsouth : anchor + southOffset ∉ P.cells :=
    hoccurs.2 southOffset (by simp [buiDPattern, southOffset])
  exact northLeafAt_of_three_forbidden hanchor hwest heast hsouth hcard

private theorem e_occursAt_northLeaf {P : Polyomino} {anchor : Cell}
    (hoccurs : buiEPattern.OccursAt P.cells anchor)
    (hcard : 2 ≤ P.cells.card) : NorthLeafAt P.cells anchor := by
  have hanchor : anchor ∈ P.cells := by
    have hrequired := hoccurs.1 (0, 0) (by simp [buiEPattern])
    rw [add_zero_offset] at hrequired
    exact hrequired
  have hwest : anchor + westOffset ∉ P.cells :=
    hoccurs.2 westOffset (by simp [buiEPattern, westOffset])
  have heast : anchor + eastOffset ∉ P.cells :=
    hoccurs.2 eastOffset (by simp [buiEPattern, eastOffset])
  have hsouth : anchor + southOffset ∉ P.cells :=
    hoccurs.2 southOffset (by simp [buiEPattern, southOffset])
  exact northLeafAt_of_three_forbidden hanchor hwest heast hsouth hcard

private theorem c_delete_occursAt_e {P : Polyomino} {anchor : Cell}
    (hoccurs : buiCPattern.OccursAt P.cells anchor)
    (hleaf : NorthLeafAt P.cells anchor) :
    buiEPattern.OccursAt (P.cells.erase anchor) (anchor + northOffset) := by
  constructor
  · intro offset hoffset
    have hoffset' : offset = (0, 0) := by
      simpa [buiEPattern] using hoffset
    subst offset
    rw [add_zero_offset]
    exact Finset.mem_erase.mpr
      ⟨add_north_ne_self anchor, hleaf.north_mem⟩
  · intro offset hoffset hmem
    simp only [buiEPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with h | h | h | h | h
    · subst offset
      change (anchor + northOffset) + westOffset ∈
        P.cells.erase anchor at hmem
      rw [add_north_add_west] at hmem
      exact hoccurs.2 (-1, 1) (by simp [buiCPattern])
        (Finset.mem_erase.mp hmem).2
    · subst offset
      change (anchor + northOffset) + eastOffset ∈
        P.cells.erase anchor at hmem
      rw [add_north_add_east] at hmem
      exact hoccurs.2 (1, 1) (by simp [buiCPattern])
        (Finset.mem_erase.mp hmem).2
    · subst offset
      rw [add_north_add_southwest] at hmem
      exact hleaf.west_not_mem (Finset.mem_erase.mp hmem).2
    · subst offset
      change (anchor + northOffset) + southOffset ∈
        P.cells.erase anchor at hmem
      rw [add_north_add_south] at hmem
      exact (Finset.mem_erase.mp hmem).1 rfl
    · subst offset
      rw [add_north_add_southeast] at hmem
      exact hleaf.east_not_mem (Finset.mem_erase.mp hmem).2

private theorem d_delete_occursAt_g {P : Polyomino} {anchor : Cell}
    (hoccurs : buiDPattern.OccursAt P.cells anchor)
    (hleaf : NorthLeafAt P.cells anchor) :
    buiGPattern.OccursAt (P.cells.erase anchor) (anchor + northOffset) := by
  constructor
  · intro offset hoffset
    have hoffset' : offset = (0, 0) := by
      simpa [buiGPattern] using hoffset
    subst offset
    rw [add_zero_offset]
    exact Finset.mem_erase.mpr
      ⟨add_north_ne_self anchor, hleaf.north_mem⟩
  · intro offset hoffset hmem
    simp only [buiGPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with h | h | h | h
    · subst offset
      change (anchor + northOffset) + westOffset ∈
        P.cells.erase anchor at hmem
      rw [add_north_add_west] at hmem
      exact hoccurs.2 (-1, 1) (by simp [buiDPattern])
        (Finset.mem_erase.mp hmem).2
    · subst offset
      rw [add_north_add_southwest] at hmem
      exact hleaf.west_not_mem (Finset.mem_erase.mp hmem).2
    · subst offset
      change (anchor + northOffset) + southOffset ∈
        P.cells.erase anchor at hmem
      rw [add_north_add_south] at hmem
      exact (Finset.mem_erase.mp hmem).1 rfl
    · subst offset
      rw [add_north_add_southeast] at hmem
      exact hleaf.east_not_mem (Finset.mem_erase.mp hmem).2

private theorem e_delete_occursAt_f {P : Polyomino} {anchor : Cell}
    (hoccurs : buiEPattern.OccursAt P.cells anchor)
    (hleaf : NorthLeafAt P.cells anchor) :
    buiFPattern.OccursAt (P.cells.erase anchor) (anchor + northOffset) := by
  constructor
  · intro offset hoffset
    have hoffset' : offset = (0, 0) := by
      simpa [buiFPattern] using hoffset
    subst offset
    rw [add_zero_offset]
    exact Finset.mem_erase.mpr
      ⟨add_north_ne_self anchor, hleaf.north_mem⟩
  · intro offset hoffset hmem
    simp only [buiFPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with h | h | h
    · subst offset
      rw [add_north_add_southwest] at hmem
      exact hleaf.west_not_mem (Finset.mem_erase.mp hmem).2
    · subst offset
      change (anchor + northOffset) + southOffset ∈
        P.cells.erase anchor at hmem
      rw [add_north_add_south] at hmem
      exact (Finset.mem_erase.mp hmem).1 rfl
    · subst offset
      rw [add_north_add_southeast] at hmem
      exact hleaf.east_not_mem (Finset.mem_erase.mp hmem).2

/-- Occurrence of an offset pattern is equivariant under translation. -/
theorem OffsetPattern.OccursAt.translate {pattern : OffsetPattern}
    {cells : Finset Cell} {anchor : Cell}
    (hoccurs : pattern.OccursAt cells anchor) (v : Cell) :
    pattern.OccursAt (cells.image fun cell => v + cell) (v + anchor) := by
  constructor
  · intro offset hoffset
    apply Finset.mem_image.mpr
    refine ⟨anchor + offset, hoccurs.1 offset hoffset, ?_⟩
    simp [add_assoc]
  · intro offset hoffset hmem
    rcases Finset.mem_image.mp hmem with ⟨cell, hcell, hcellEq⟩
    have hcancel : cell = anchor + offset := by
      apply add_left_cancel (a := v)
      simpa [add_assoc] using hcellEq
    exact hoccurs.2 offset hoffset (hcancel ▸ hcell)

/-! ## The injective map on globally marked occurrences -/

/-- A normalized polyomino together with one marked occurrence of a named
neighborhood.  Its cardinality is the aggregate occurrence count. -/
abbrev MarkedOccurrence (kind : BuiNeighborhood) (n : ℕ) :=
  Σ P : NormalizedPolyomino n,
    { anchor : Cell //
      anchor ∈ kind.pattern.occurrenceAnchors P.toPolyomino.cells }

private theorem card_markedOccurrence (kind : BuiNeighborhood) (n : ℕ) :
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

/-- A normalized polyomino with one explicitly certified north-attached leaf. -/
structure NorthLeafOccurrence (n : ℕ) where
  polyomino : NormalizedPolyomino n
  anchor : Cell
  leaf : NorthLeafAt polyomino.toPolyomino.cells anchor

namespace NorthLeafOccurrence

@[ext]
theorem ext {n : ℕ} {x y : NorthLeafOccurrence n}
    (hpolyomino : x.polyomino = y.polyomino)
    (hanchor : x.anchor = y.anchor) : x = y := by
  cases x
  cases y
  cases hpolyomino
  cases hanchor
  rfl

/-- The polyomino remaining after the marked leaf is removed. -/
def erased {n : ℕ} (x : NorthLeafOccurrence n) : Polyomino :=
  x.polyomino.toPolyomino.eraseNorthLeaf x.anchor x.leaf

/-- The vector which southwest-normalizes the remainder. -/
noncomputable def normalizationVector {n : ℕ} (x : NorthLeafOccurrence n) : Cell :=
  -x.erased.southwestAnchor

/-- The normalized `(n - 1)`-cell remainder. -/
noncomputable def normalizedRemainder {n : ℕ} (x : NorthLeafOccurrence n) :
    NormalizedPolyomino (n - 1) where
  toPolyomino := x.erased.translate x.normalizationVector
  southwestAnchor_eq := by
    rw [Polyomino.southwestAnchor_translate]
    apply Prod.ext <;> simp [normalizationVector]
  card_cells := by
    rw [Polyomino.card_cells_translate]
    change (x.polyomino.toPolyomino.cells.erase x.anchor).card = n - 1
    rw [Finset.card_erase_of_mem x.leaf.anchor_mem,
      x.polyomino.card_cells]

/-- Delete and normalize, retaining the translated north neighbor as the
marked cell. -/
noncomputable def deleteData {n : ℕ} (x : NorthLeafOccurrence n) :
    NormalizedPolyomino (n - 1) × Cell :=
  (x.normalizedRemainder,
    x.normalizationVector + (x.anchor + northOffset))

private def reconstructedCells {n : ℕ}
    (out : NormalizedPolyomino n × Cell) : Finset Cell :=
  insert (out.2 + southOffset) out.1.toPolyomino.cells

private theorem insert_image_erase (cells : Finset Cell) {anchor : Cell}
    (hanchor : anchor ∈ cells) (v : Cell) :
    insert (v + anchor) ((cells.erase anchor).image fun cell => v + cell) =
      cells.image fun cell => v + cell := by
  ext cell
  constructor
  · intro hcell
    rw [Finset.mem_insert] at hcell
    rcases hcell with hcell | hcell
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
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr
        ⟨other, Finset.mem_erase.mpr ⟨hEq, hother⟩, rfl⟩

private theorem reconstructedCells_deleteData {n : ℕ}
    (x : NorthLeafOccurrence n) :
    reconstructedCells x.deleteData =
      (x.polyomino.toPolyomino.translate x.normalizationVector).cells := by
  change insert
      ((x.normalizationVector + (x.anchor + northOffset)) + southOffset)
      ((x.polyomino.toPolyomino.cells.erase x.anchor).image
        fun cell => x.normalizationVector + cell) =
    x.polyomino.toPolyomino.cells.image
      (fun cell => x.normalizationVector + cell)
  rw [show (x.normalizationVector + (x.anchor + northOffset)) + southOffset =
      x.normalizationVector + x.anchor by
        rw [← add_assoc, add_north_add_south]]
  exact insert_image_erase _ x.leaf.anchor_mem _

/-- Deletion, normalization, and retention of the north mark lose no
information about a normalized marked leaf. -/
theorem deleteData_injective (n : ℕ) :
    Function.Injective (deleteData : NorthLeafOccurrence n →
      NormalizedPolyomino (n - 1) × Cell) := by
  intro x y hdelete
  have hreconstruct := congrArg reconstructedCells hdelete
  rw [reconstructedCells_deleteData, reconstructedCells_deleteData] at hreconstruct
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
  change x.normalizationVector + (x.anchor + northOffset) =
      y.normalizationVector + (y.anchor + northOffset) at hmarks
  rw [hvectors] at hmarks
  have hanchors : x.anchor + northOffset = y.anchor + northOffset :=
    add_left_cancel hmarks
  have hanchor : x.anchor = y.anchor := add_right_cancel hanchors
  exact NorthLeafOccurrence.ext hpolyomino hanchor

end NorthLeafOccurrence

/-- The reusable geometric interface for a deletion rule from `source` to
`target`. -/
structure NorthDeletionRule (source target : BuiNeighborhood) where
  leaf_of_occursAt : ∀ {P : Polyomino} {anchor : Cell},
    source.pattern.OccursAt P.cells anchor → 2 ≤ P.cells.card →
      NorthLeafAt P.cells anchor
  target_after_erase : ∀ {P : Polyomino} {anchor : Cell},
    source.pattern.OccursAt P.cells anchor →
    ∀ hleaf : NorthLeafAt P.cells anchor,
      target.pattern.OccursAt (P.cells.erase anchor) (anchor + northOffset)

namespace NorthDeletionRule

private theorem marked_occursAt {kind : BuiNeighborhood} {n : ℕ}
    (x : MarkedOccurrence kind n) :
    kind.pattern.OccursAt x.1.toPolyomino.cells x.2.1 := by
  classical
  have hx := x.2.2
  change x.2.1 ∈ x.1.toPolyomino.cells.filter
    (fun anchor => kind.pattern.OccursAt x.1.toPolyomino.cells anchor) at hx
  exact (Finset.mem_filter.mp hx).2

noncomputable def sourceLeaf {source target : BuiNeighborhood} {n : ℕ}
    (rule : NorthDeletionRule source target) (hn : 2 ≤ n)
    (x : MarkedOccurrence source n) : NorthLeafOccurrence n where
  polyomino := x.1
  anchor := x.2.1
  leaf := rule.leaf_of_occursAt (marked_occursAt x) (by
    simpa only [x.1.card_cells] using hn)

private theorem sourceLeaf_injective {source target : BuiNeighborhood} {n : ℕ}
    (rule : NorthDeletionRule source target) (hn : 2 ≤ n) :
    Function.Injective (rule.sourceLeaf hn) := by
  intro x y h
  have hP : x.1 = y.1 := congrArg NorthLeafOccurrence.polyomino h
  have ha : x.2.1 = y.2.1 := congrArg NorthLeafOccurrence.anchor h
  cases x with
  | mk P anchor =>
      cases y with
      | mk Q other =>
          dsimp at hP ha
          cases hP
          have hanchor : anchor = other := Subtype.ext ha
          cases hanchor
          rfl

/-- The deletion injection from marked `source` occurrences on `n` cells to
marked `target` occurrences on `n - 1` cells. -/
noncomputable def markedMap {source target : BuiNeighborhood} {n : ℕ}
    (rule : NorthDeletionRule source target) (hn : 2 ≤ n) :
    MarkedOccurrence source n → MarkedOccurrence target (n - 1) := fun x => by
  classical
  let leaf := rule.sourceLeaf hn x
  let out := leaf.deleteData
  refine ⟨out.1, ⟨out.2, ?_⟩⟩
  change out.2 ∈ out.1.toPolyomino.cells.filter
    (fun anchor => target.pattern.OccursAt out.1.toPolyomino.cells anchor)
  rw [Finset.mem_filter]
  have hnorthErase : leaf.anchor + northOffset ∈
      leaf.polyomino.toPolyomino.cells.erase leaf.anchor :=
    Finset.mem_erase.mpr
      ⟨add_north_ne_self leaf.anchor, leaf.leaf.north_mem⟩
  have hanchorNormalized : out.2 ∈ out.1.toPolyomino.cells := by
    change leaf.normalizationVector + (leaf.anchor + northOffset) ∈
      (leaf.polyomino.toPolyomino.cells.erase leaf.anchor).image
        (fun cell => leaf.normalizationVector + cell)
    exact Finset.mem_image.mpr
      ⟨leaf.anchor + northOffset, hnorthErase, rfl⟩
  refine ⟨hanchorNormalized, ?_⟩
  have hraw := rule.target_after_erase (marked_occursAt x) leaf.leaf
  change target.pattern.OccursAt
    ((leaf.polyomino.toPolyomino.cells.erase leaf.anchor).image
      fun cell => leaf.normalizationVector + cell)
    (leaf.normalizationVector + (leaf.anchor + northOffset))
  exact hraw.translate leaf.normalizationVector

theorem markedMap_injective {source target : BuiNeighborhood} {n : ℕ}
    (rule : NorthDeletionRule source target) (hn : 2 ≤ n) :
    Function.Injective (rule.markedMap hn) := by
  intro x y hxy
  have hdata := congrArg
    (fun z : MarkedOccurrence target (n - 1) => (z.1, z.2.1)) hxy
  change (rule.sourceLeaf hn x).deleteData =
    (rule.sourceLeaf hn y).deleteData at hdata
  have hleaf := NorthLeafOccurrence.deleteData_injective n hdata
  exact rule.sourceLeaf_injective hn hleaf

theorem aggregateOccurrenceCount_le {source target : BuiNeighborhood} {n : ℕ}
    (rule : NorthDeletionRule source target) (hn : 2 ≤ n) :
    source.aggregateOccurrenceCount n ≤
      target.aggregateOccurrenceCount (n - 1) := by
  rw [← card_markedOccurrence, ← card_markedOccurrence]
  exact Fintype.card_le_of_injective (rule.markedMap hn)
    (rule.markedMap_injective hn)

theorem coefficient_le {source target : BuiNeighborhood} {n : ℕ}
    (rule : NorthDeletionRule source target) (hn : 2 ≤ n) :
    source.coefficient n ≤ target.coefficient (n - 1) := by
  change (source.aggregateOccurrenceCount n : ℚ) ≤
    (target.aggregateOccurrenceCount (n - 1) : ℚ)
  exact_mod_cast (rule.aggregateOccurrenceCount_le hn)

end NorthDeletionRule

private theorem cToEDeletionRule :
    NorthDeletionRule BuiNeighborhood.c BuiNeighborhood.e where
  leaf_of_occursAt := c_occursAt_northLeaf
  target_after_erase := c_delete_occursAt_e

private theorem dToGDeletionRule :
    NorthDeletionRule BuiNeighborhood.d BuiNeighborhood.g where
  leaf_of_occursAt := d_occursAt_northLeaf
  target_after_erase := d_delete_occursAt_g

private theorem eToFDeletionRule :
    NorthDeletionRule BuiNeighborhood.e BuiNeighborhood.f where
  leaf_of_occursAt := e_occursAt_northLeaf
  target_after_erase := e_delete_occursAt_f

/-! ## Aggregate and coefficient forms used by the published system -/

theorem buiC_aggregateOccurrenceCount_le_e_pred {n : ℕ} (hn : 2 ≤ n) :
    BuiNeighborhood.c.aggregateOccurrenceCount n ≤
      BuiNeighborhood.e.aggregateOccurrenceCount (n - 1) :=
  cToEDeletionRule.aggregateOccurrenceCount_le hn

theorem buiD_aggregateOccurrenceCount_le_g_pred {n : ℕ} (hn : 2 ≤ n) :
    BuiNeighborhood.d.aggregateOccurrenceCount n ≤
      BuiNeighborhood.g.aggregateOccurrenceCount (n - 1) :=
  dToGDeletionRule.aggregateOccurrenceCount_le hn

theorem buiE_aggregateOccurrenceCount_le_f_pred {n : ℕ} (hn : 2 ≤ n) :
    BuiNeighborhood.e.aggregateOccurrenceCount n ≤
      BuiNeighborhood.f.aggregateOccurrenceCount (n - 1) :=
  eToFDeletionRule.aggregateOccurrenceCount_le hn

/-- The `C` recurrence in exactly the positive-index form expected by
`PublishedBuiRecurrences`. -/
theorem buiC_coefficient_le_e_pred {n : ℕ} (hn : 2 ≤ n) :
    BuiNeighborhood.c.coefficient n ≤
      BuiNeighborhood.e.coefficient (n - 1) :=
  cToEDeletionRule.coefficient_le hn

/-- The `D` recurrence in exactly the positive-index form expected by
`PublishedBuiRecurrences`. -/
theorem buiD_coefficient_le_g_pred {n : ℕ} (hn : 2 ≤ n) :
    BuiNeighborhood.d.coefficient n ≤
      BuiNeighborhood.g.coefficient (n - 1) :=
  dToGDeletionRule.coefficient_le hn

/-- The `E` recurrence in exactly the positive-index form expected by
`PublishedBuiRecurrences`. -/
theorem buiE_coefficient_le_f_pred {n : ℕ} (hn : 2 ≤ n) :
    BuiNeighborhood.e.coefficient n ≤
      BuiNeighborhood.f.coefficient (n - 1) :=
  eToFDeletionRule.coefficient_le hn

/-! ## Literal Kronecker-delta forms, including the boundary indices -/

private theorem normalizedPolyomino_zero_false
    (P : NormalizedPolyomino 0) : False := by
  have hpositive : 0 < P.toPolyomino.cells.card :=
    Finset.card_pos.mpr P.toPolyomino.nonempty
  rw [P.card_cells] at hpositive
  omega

private theorem aggregateOccurrenceCount_zero (kind : BuiNeighborhood) :
    kind.aggregateOccurrenceCount 0 = 0 := by
  classical
  unfold BuiNeighborhood.aggregateOccurrenceCount
  apply Finset.sum_eq_zero
  intro P _
  exact (normalizedPolyomino_zero_false P).elim

private theorem coefficient_zero (kind : BuiNeighborhood) :
    kind.coefficient 0 = 0 := by
  change (kind.aggregateOccurrenceCount 0 : ℚ) = 0
  exact_mod_cast (aggregateOccurrenceCount_zero kind)

private theorem normalizedPolyomino_one_cells
    (P : NormalizedPolyomino 1) :
    P.toPolyomino.cells = {(0, 0)} := by
  obtain ⟨anchor, hcells⟩ := Finset.card_eq_one.mp P.card_cells
  have horigin : (0, 0) ∈ ({anchor} : Finset Cell) := by
    rw [← hcells]
    exact P.origin_mem
  have hanchor : anchor = (0, 0) := by
    have horiginEq : (0, 0) = anchor := by
      simpa only [Finset.mem_singleton] using horigin
    exact horiginEq.symm
  simpa [hanchor] using hcells

private theorem normalizedPolyomino_one_subsingleton
    (P Q : NormalizedPolyomino 1) : P = Q := by
  apply NormalizedPolyomino.ext
  apply Polyomino.ext
  rw [normalizedPolyomino_one_cells P, normalizedPolyomino_one_cells Q]

private theorem markedOccurrence_one_subsingleton (kind : BuiNeighborhood)
    (x y : MarkedOccurrence kind 1) : x = y := by
  classical
  rcases x with ⟨P, ⟨anchor, hanchor⟩⟩
  rcases y with ⟨Q, ⟨other, hother⟩⟩
  have hPQ := normalizedPolyomino_one_subsingleton P Q
  subst Q
  change anchor ∈ P.toPolyomino.cells.filter
    (fun cell => kind.pattern.OccursAt P.toPolyomino.cells cell) at hanchor
  change other ∈ P.toPolyomino.cells.filter
    (fun cell => kind.pattern.OccursAt P.toPolyomino.cells cell) at hother
  have hanchorMem : anchor ∈ P.toPolyomino.cells :=
    (Finset.mem_filter.mp hanchor).1
  have hotherMem : other ∈ P.toPolyomino.cells :=
    (Finset.mem_filter.mp hother).1
  rw [normalizedPolyomino_one_cells P] at hanchorMem hotherMem
  simp only [Finset.mem_singleton] at hanchorMem hotherMem
  subst anchor
  subst other
  rfl

private theorem aggregateOccurrenceCount_one_le_one (kind : BuiNeighborhood) :
    kind.aggregateOccurrenceCount 1 ≤ 1 := by
  rw [← card_markedOccurrence]
  have hinjective : Function.Injective
      (fun _ : MarkedOccurrence kind 1 => ()) := by
    intro x y _
    exact markedOccurrence_one_subsingleton kind x y
  have hcard := Fintype.card_le_of_injective
    (fun _ : MarkedOccurrence kind 1 => ()) hinjective
  simpa using hcard

private theorem coefficient_one_le_one (kind : BuiNeighborhood) :
    kind.coefficient 1 ≤ 1 := by
  change (kind.aggregateOccurrenceCount 1 : ℚ) ≤ 1
  exact_mod_cast (aggregateOccurrenceCount_one_le_one kind)

/-- Literal all-index form `C(n) <= delta_(n,1) + E(n-1)`. -/
theorem buiC_coefficient_le_delta_add_e_pred (n : ℕ) :
    BuiNeighborhood.c.coefficient n ≤
      (if n = 1 then 1 else 0) +
        BuiNeighborhood.e.coefficient (n - 1) := by
  by_cases hn : 2 ≤ n
  · have hn1 : n ≠ 1 := by omega
    simpa [hn1] using buiC_coefficient_le_e_pred hn
  · have hsmall : n = 0 ∨ n = 1 := by omega
    rcases hsmall with rfl | rfl
    · simp [coefficient_zero]
    · simpa [coefficient_zero] using
        coefficient_one_le_one BuiNeighborhood.c

/-- Literal all-index form `D(n) <= delta_(n,1) + G(n-1)`. -/
theorem buiD_coefficient_le_delta_add_g_pred (n : ℕ) :
    BuiNeighborhood.d.coefficient n ≤
      (if n = 1 then 1 else 0) +
        BuiNeighborhood.g.coefficient (n - 1) := by
  by_cases hn : 2 ≤ n
  · have hn1 : n ≠ 1 := by omega
    simpa [hn1] using buiD_coefficient_le_g_pred hn
  · have hsmall : n = 0 ∨ n = 1 := by omega
    rcases hsmall with rfl | rfl
    · simp [coefficient_zero]
    · simpa [coefficient_zero] using
        coefficient_one_le_one BuiNeighborhood.d

/-- Literal all-index form `E(n) <= delta_(n,1) + F(n-1)`. -/
theorem buiE_coefficient_le_delta_add_f_pred (n : ℕ) :
    BuiNeighborhood.e.coefficient n ≤
      (if n = 1 then 1 else 0) +
        BuiNeighborhood.f.coefficient (n - 1) := by
  by_cases hn : 2 ≤ n
  · have hn1 : n ≠ 1 := by omega
    simpa [hn1] using buiE_coefficient_le_f_pred hn
  · have hsmall : n = 0 ∨ n = 1 := by omega
    rcases hsmall with rfl | rfl
    · simp [coefficient_zero]
    · simpa [coefficient_zero] using
        coefficient_one_le_one BuiNeighborhood.e

end LeanProofs.KlarnerConstant
