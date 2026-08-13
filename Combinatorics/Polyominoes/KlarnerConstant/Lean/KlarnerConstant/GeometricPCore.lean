import KlarnerConstant.GeometricPBasics
import KlarnerConstant.SeededPartition

/-!
# Marked-territory and seeded-partition infrastructure for the P recurrence

This module contains the oriented-occurrence and common seeded-partition
machinery shared by the five geometric branches.  Coordinate and orientation
infrastructure is isolated in GeometricPBasics; branch-specific seed systems
live in GeometricPGeometry, and the finite Cauchy-product encoding lives in
GeometricPEndpoint.
-/

namespace LeanProofs.KlarnerConstant

/-! ## Generic oriented territory occurrences -/

/-- A territory with a distinguished physical anchor and an orientation into
the standard coordinate system of a Bui pattern. -/
structure OrientedTerritoryOccurrence (kind : BuiNeighborhood) where
  territory : Polyomino
  physicalAnchor : Cell
  orientation : GridOrientation
  occurs : kind.pattern.OccursAt
    (orientation.mapCells
      (territory.translate (-physicalAnchor)).cells) 0

namespace OrientedTerritoryOccurrence

private theorem zero_mem_required (kind : BuiNeighborhood) :
    (0, 0) ∈ kind.pattern.required := by
  cases kind <;> simp [BuiNeighborhood.pattern, buiCPattern, buiDPattern,
    buiEPattern, buiFPattern, buiGPattern, buiHPattern, buiPPattern,
    buiQPattern, buiRPattern, buiSPattern, buiTPattern, buiUPattern,
    buiVPattern, buiWPattern, buiXPattern, buiYPattern, buiZPattern]

/-- The oriented, translated cell set appearing in `occurs` really is a
polyomino. -/
def orientedPolyomino {kind : BuiNeighborhood}
    (x : OrientedTerritoryOccurrence kind) : Polyomino where
  cells := x.orientation.mapCells
    (x.territory.translate (-x.physicalAnchor)).cells
  nonempty := by
    rcases x.territory.nonempty with ⟨c, hc⟩
    refine ⟨x.orientation.map (-x.physicalAnchor + c), ?_⟩
    exact Finset.mem_image.mpr ⟨-x.physicalAnchor + c,
      Finset.mem_image.mpr ⟨c, hc, rfl⟩, rfl⟩
  edgeConnected := x.orientation.edgeConnected_mapCells
    (x.territory.translate (-x.physicalAnchor)).edgeConnected

/-- Canonically normalize an oriented territory, retaining the transformed
physical anchor as the marked occurrence. -/
noncomputable def toMarkedOccurrence {kind : BuiNeighborhood}
    (x : OrientedTerritoryOccurrence kind) :
    MarkedOccurrence kind x.territory.cells.card := by
  classical
  let Q := x.orientedPolyomino
  let v := -Q.southwestAnchor
  let N : NormalizedPolyomino x.territory.cells.card := {
    toPolyomino := Q.translate v
    southwestAnchor_eq := by
      rw [Polyomino.southwestAnchor_translate]
      apply Prod.ext <;> simp [v]
    card_cells := by
      rw [Polyomino.card_cells_translate]
      change (x.orientation.mapCells
        (x.territory.translate (-x.physicalAnchor)).cells).card =
          x.territory.cells.card
      rw [GridOrientation.card_mapCells,
        Polyomino.card_cells_translate] }
  have hzero : ((0, 0) : Cell) ∈ Q.cells := by
    change ((0, 0) : Cell) ∈
      (x.orientation.mapCells
        (x.territory.translate (-x.physicalAnchor)).cells)
    simpa only [zero_add] using
      x.occurs.1 ((0, 0) : Cell) (by simpa using zero_mem_required kind)
  refine ⟨N, ⟨v, ?_⟩⟩
  rw [OffsetPattern.occurrenceAnchors, Finset.mem_filter]
  constructor
  · change v ∈ (Q.translate v).cells
    rw [Polyomino.mem_translate_cells]
    have hv : v - v = ((0, 0) : Cell) := by
      apply Prod.ext <;> simp
    rw [hv]
    exact hzero
  · change kind.pattern.OccursAt (Q.translate v).cells v
    rw [Polyomino.cells_translate]
    simpa only [Q, orientedPolyomino, add_zero] using x.occurs.translate v

@[simp]
theorem toMarkedOccurrence_polyomino {kind : BuiNeighborhood}
    (x : OrientedTerritoryOccurrence kind) :
    x.toMarkedOccurrence.1.toPolyomino =
      x.orientedPolyomino.translate (-x.orientedPolyomino.southwestAnchor) :=
  rfl

@[simp]
theorem toMarkedOccurrence_anchor {kind : BuiNeighborhood}
    (x : OrientedTerritoryOccurrence kind) :
    x.toMarkedOccurrence.2.1 = -x.orientedPolyomino.southwestAnchor :=
  rfl

/-- Undo a target normalization and orientation, placing the raw occurrence
anchor at a prescribed offset from the source occurrence anchor. -/
def recoverMarkedTerritory {kind : BuiNeighborhood} {n : ℕ}
    (o : GridOrientation) (physicalAnchorOffset : Cell)
    (out : MarkedOccurrence kind n) : Finset Cell :=
  out.1.toPolyomino.cells.image fun c ↦
    physicalAnchorOffset + o.inv (c - out.2.1)

/-- `toMarkedOccurrence` is lossless once the fixed orientation and the
physical anchor's offset from the source anchor are supplied. -/
theorem recover_toMarkedOccurrence {kind : BuiNeighborhood}
    (x : OrientedTerritoryOccurrence kind) (sourceAnchor offset : Cell)
    (hphysical : x.physicalAnchor = sourceAnchor + offset) :
    recoverMarkedTerritory x.orientation offset x.toMarkedOccurrence =
      x.territory.cells.image (fun c ↦ -sourceAnchor + c) := by
  classical
  let Q := x.orientedPolyomino
  change
    (Q.translate (-Q.southwestAnchor)).cells.image
        (fun c ↦ offset + x.orientation.inv
          (c - (-Q.southwestAnchor))) =
      x.territory.cells.image (fun c ↦ -sourceAnchor + c)
  rw [Polyomino.cells_translate]
  rw [Finset.image_image]
  calc
    Q.cells.image
        ((fun c ↦ offset + x.orientation.inv
          (c - (-Q.southwestAnchor))) ∘
          fun c ↦ -Q.southwestAnchor + c) =
        Q.cells.image (fun c ↦ offset + x.orientation.inv c) := by
      apply Finset.image_congr
      intro c hc
      dsimp only [Function.comp_apply]
      have hcancel :
          (-Q.southwestAnchor + c) - (-Q.southwestAnchor) = c := by
        apply Prod.ext <;> simp
      rw [hcancel]
    _ = x.territory.cells.image (fun c ↦ -sourceAnchor + c) := by
      change
        (x.orientation.mapCells
          (x.territory.translate (-x.physicalAnchor)).cells).image
            (fun c ↦ offset + x.orientation.inv c) = _
      simp only [GridOrientation.mapCells, Polyomino.cells_translate,
        Finset.image_image]
      apply Finset.image_congr
      intro c hc
      dsimp only [Function.comp_apply]
      rw [x.orientation.inv_map, hphysical]
      apply Prod.ext <;> dsimp <;> omega

end OrientedTerritoryOccurrence

open OrientedTerritoryOccurrence

/-! ## A generic marked pattern proof from physical required/forbidden cells -/

theorem oriented_occursAt_of_physical
    (pattern : OffsetPattern) (cells : Finset Cell) (anchor : Cell)
    (o : GridOrientation)
    (hrequired : ∀ offset ∈ pattern.required,
      anchor + o.inv offset ∈ cells)
    (hforbidden : ∀ offset ∈ pattern.forbidden,
      anchor + o.inv offset ∉ cells) :
    pattern.OccursAt
      (o.mapCells ((cells.image fun c ↦ -anchor + c))) 0 := by
  constructor
  · intro offset hoffset
    have hraw := hrequired offset hoffset
    apply Finset.mem_image.mpr
    refine ⟨o.inv offset, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨anchor + o.inv offset, hraw, ?_⟩
      apply Prod.ext <;> simp [add_assoc]
    · simpa using o.map_inv offset
  · intro offset hoffset hmem
    rcases Finset.mem_image.mp hmem with ⟨d, hd, hdo⟩
    rcases Finset.mem_image.mp hd with ⟨c, hc, hcd⟩
    have hd0 : d = o.inv offset := by
      apply o.map_injective
      calc
        o.map d = 0 + offset := hdo
        _ = offset := zero_add offset
        _ = o.map (o.inv offset) := (o.map_inv offset).symm
    have hcEq : c = anchor + o.inv offset := by
      apply add_left_cancel (a := -anchor)
      rw [hcd, hd0]
      apply Prod.ext <;> simp [add_assoc]
    exact hforbidden offset hoffset (hcEq ▸ hc)

/-! ## Reaching a seed from a connected polyomino -/

/-- If the union of the designated seeds contains at least one cell of a
connected ambient polyomino, then every ambient cell reaches a seed. -/
theorem reaches_some_seed_of_connected {i : Type*} [Fintype i]
    [DecidableEq i] {P : Polyomino} {seeds : i → Finset Cell}
    (hseed : ∃ j s, s ∈ seeds j ∧ s ∈ P.cells) :
    ∀ c, c ∈ P.cells →
      ∃ j s, s ∈ seeds j ∧
        Relation.ReflTransGen (EdgeAdjacentIn P.cells) c s := by
  intro c hc
  rcases hseed with ⟨j, s, hs, hsP⟩
  exact ⟨j, s, hs, P.edgeConnected c hc s hsP⟩

/-! ## Branch data and the common partition output -/

/-- Everything needed to apply the finite seeded-partition theorem to one
local branch.  Seeds may contain several already-connected forced cells. -/
structure PBranchSeeds (k : ℕ) where
  polyomino : Polyomino
  anchor : Cell
  kinds : Fin k → BuiNeighborhood
  seeds : Fin k → Finset Cell
  orientations : Fin k → GridOrientation
  physicalAnchors : Fin k → Cell
  seed_subset : ∀ i, seeds i ⊆ polyomino.cells
  seed_nonempty : ∀ i, (seeds i).Nonempty
  seed_connected : ∀ i, EdgeConnected (seeds i)
  seed_pairwise_disjoint : Set.PairwiseDisjoint Set.univ seeds
  index_nonempty : 0 < k
  physicalAnchor_mem : ∀ i, physicalAnchors i ∈ seeds i
  required_mem : ∀ i offset, offset ∈ (kinds i).pattern.required →
    physicalAnchors i + (orientations i).inv offset ∈ seeds i
  forbidden_avoided : ∀ i offset,
    offset ∈ (kinds i).pattern.forbidden →
    physicalAnchors i + (orientations i).inv offset ∉ polyomino.cells ∨
      ∃ j, j ≠ i ∧
        physicalAnchors i + (orientations i).inv offset ∈ seeds j

namespace PBranchSeeds

/-- The abstract seed system associated with branch data.  Connectedness of
the whole source means a single nonempty seed is enough to establish the
component-meeting condition. -/
def seedSystem {k : ℕ} (D : PBranchSeeds k) : SeedSystem (Fin k) where
  cells := D.polyomino.cells
  seeds := D.seeds
  seed_subset := D.seed_subset
  seed_nonempty := D.seed_nonempty
  seed_connected := D.seed_connected
  seed_pairwise_disjoint := by
    intro i j hij
    exact D.seed_pairwise_disjoint (by simp) (by simp) hij
  reaches_seed := by
    have hseed : ∃ j s, s ∈ D.seeds j ∧ s ∈ D.polyomino.cells := by
      let j : Fin k := ⟨0, D.index_nonempty⟩
      rcases D.seed_nonempty j with ⟨s, hs⟩
      exact ⟨j, s, hs, D.seed_subset j hs⟩
    exact reaches_some_seed_of_connected hseed

/-- The selected connected partition of a concrete branch. -/
noncomputable def partition {k : ℕ} (D : PBranchSeeds k) :
    SeededPartition D.seedSystem :=
  D.seedSystem.choosePartition

/-- A territory produced from branch data has the advertised oriented Bui
neighborhood.  Forbidden cells are either globally absent or belong to a
foreign seed and therefore to a foreign territory. -/
noncomputable def territoryOccurrence {k : ℕ} (D : PBranchSeeds k)
    (i : Fin k) : OrientedTerritoryOccurrence (D.kinds i) := by
  let part := D.partition
  let territory := part.territoryPolyomino i
  refine {
    territory := territory
    physicalAnchor := D.physicalAnchors i
    orientation := D.orientations i
    occurs := ?_ }
  apply oriented_occursAt_of_physical
  · intro offset hoffset
    exact part.seed_subset i (D.required_mem i offset hoffset)
  · intro offset hoffset
    rcases D.forbidden_avoided i offset hoffset with habsent | hforeign
    · exact fun hterritory ↦ habsent (part.territory_subset i hterritory)
    · rcases hforeign with ⟨j, hji, hseed⟩
      exact fun hterritory ↦
        (Finset.disjoint_left.mp (part.disjoint_foreign_seed hji.symm))
          hterritory hseed

/-- The territories cover the complete source polyomino. -/
theorem partition_cover {k : ℕ} (D : PBranchSeeds k) :
    coveredCells D.partition.territories = D.polyomino.cells :=
  D.partition.cover

/-- Exact cardinal additivity for the connected territories.  This is the
index equation used by the Cauchy-product codomain. -/
theorem partition_card_sum {k : ℕ} (D : PBranchSeeds k) :
    ∑ i : Fin k, (D.partition.territories i).card =
      D.polyomino.cells.card := by
  classical
  rw [← D.partition_cover]
  unfold coveredCells
  symm
  exact Finset.card_biUnion (by
    intro i hi j hj hij
    exact D.partition.territory_pairwise_disjoint i j hij)

/-- Equality of every territory implies equality of the original source cell
set, independently of which valid frontier-growth partition was selected. -/
theorem source_cells_of_territories_eq {k : ℕ} {D E : PBranchSeeds k}
    (h : ∀ i, D.partition.territories i = E.partition.territories i) :
    D.polyomino.cells = E.polyomino.cells := by
  rw [← D.partition_cover, ← E.partition_cover]
  unfold coveredCells
  apply Finset.biUnion_congr rfl
  intro i _
  exact h i

end PBranchSeeds

end LeanProofs.KlarnerConstant
