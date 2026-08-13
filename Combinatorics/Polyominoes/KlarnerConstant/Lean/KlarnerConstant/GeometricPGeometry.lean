import KlarnerConstant.GeometricPCore

/-!
# The five seeded geometric branches of the `P` recurrence

This module constructs the five branch seed systems, their connected
territories, and the normalized marked outputs.  It also proves exhaustive
branching and exact reconstruction/cardinality facts.  The final finite-type
encoding is isolated in `GeometricPEndpoint`.
-/

namespace LeanProofs.KlarnerConstant

open OrientedTerritoryOccurrence

/-! ## Canonical anchored reconstruction -/

/-- Translate a branch source so that its marked `P` anchor is the origin. -/
def PBranchSeeds.anchoredSourceCells {k : ℕ} (D : PBranchSeeds k) :
    Finset Cell :=
  D.polyomino.cells.image fun c ↦ -D.anchor + c

/-- Translate every selected territory to the same anchored frame. -/
noncomputable def PBranchSeeds.anchoredTerritory {k : ℕ} (D : PBranchSeeds k)
    (i : Fin k) : Finset Cell :=
  (D.partition.territories i).image fun c ↦ -D.anchor + c

theorem PBranchSeeds.anchored_cover {k : ℕ} (D : PBranchSeeds k) :
    coveredCells D.anchoredTerritory = D.anchoredSourceCells := by
  ext c
  constructor
  · intro hc
    rcases mem_coveredCells.mp hc with ⟨i, hci⟩
    rcases Finset.mem_image.mp hci with ⟨d, hd, rfl⟩
    exact Finset.mem_image.mpr
      ⟨d, D.partition.territory_subset i hd, rfl⟩
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨d, hd, rfl⟩
    rcases D.partition.mem_cells_iff_exists_territory.mp hd with ⟨i, hdi⟩
    exact mem_coveredCells.mpr ⟨i, Finset.mem_image.mpr ⟨d, hdi, rfl⟩⟩

/-- Reconstruct the anchored source from the selected physical territory cell
sets.  After the target normalizations and orientations are undone, this is the
equality used by the eventual global injectivity proof. -/
theorem PBranchSeeds.reconstruct_anchored {k : ℕ} (D : PBranchSeeds k) :
    coveredCells (fun i ↦
      (D.territoryOccurrence i).territory.cells.image
        (fun c ↦ -D.anchor + c)) = D.anchoredSourceCells := by
  exact D.anchored_cover

/-- Equality of anchored sources recovers both a normalized source polyomino
and its marked anchor. -/
theorem normalized_marked_source_injective {kind : BuiNeighborhood} {n : ℕ}
    {x y : MarkedOccurrence kind n}
    (h : x.1.toPolyomino.cells.image (fun c ↦ -x.2.1 + c) =
      y.1.toPolyomino.cells.image (fun c ↦ -y.2.1 + c)) :
    x = y := by
  have hpolyTranslate :
      x.1.toPolyomino.translate (-x.2.1) =
        y.1.toPolyomino.translate (-y.2.1) :=
    Polyomino.ext h
  have hnorm := congrArg Polyomino.normalize hpolyTranslate
  rw [Polyomino.normalize_translate, Polyomino.normalize_translate,
    x.1.normalize_toPolyomino, y.1.normalize_toPolyomino] at hnorm
  have hpoly : x.1 = y.1 := NormalizedPolyomino.ext hnorm
  have hsouthwest := congrArg Polyomino.southwestAnchor hpolyTranslate
  rw [Polyomino.southwestAnchor_translate,
    Polyomino.southwestAnchor_translate,
    x.1.southwestAnchor_eq, y.1.southwestAnchor_eq] at hsouthwest
  have hanchor : x.2.1 = y.2.1 := by
    have hneg : -x.2.1 = -y.2.1 := by simpa using hsouthwest
    exact neg_injective hneg
  cases x with
  | mk P a =>
      cases y with
      | mk Q b =>
          dsimp at hpoly hanchor
          cases hpoly
          cases Subtype.ext hanchor
          rfl

/-! ## Small finite seed lemmas -/

private theorem edgeConnected_singleton (c : Cell) : EdgeConnected {c} := by
  intro a ha b hb
  simp only [Finset.mem_singleton] at ha hb
  subst a
  subst b
  exact Relation.ReflTransGen.refl

private theorem edgeConnected_pair {a b : Cell} (hab : EdgeAdjacent a b) :
    EdgeConnected {a, b} := by
  intro x hx y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single
      ⟨by simp, by simp, hab⟩
  · exact Relation.ReflTransGen.single
      ⟨by simp, by simp, edgeAdjacent_symm hab⟩
  · exact Relation.ReflTransGen.refl

private theorem edgePath_mono_insert_p {t : Finset Cell} {x a b : Cell}
    (h : Relation.ReflTransGen (EdgeAdjacentIn t) a b) :
    Relation.ReflTransGen (EdgeAdjacentIn (insert x t)) a b := by
  exact Relation.ReflTransGen.mono
    (r := EdgeAdjacentIn t) (p := EdgeAdjacentIn (insert x t))
    (fun _ _ huv ↦ ⟨Finset.mem_insert_of_mem huv.1,
      Finset.mem_insert_of_mem huv.2.1, huv.2.2⟩) a b h

private theorem edgeConnected_insert_adjacent_p {t : Finset Cell}
    (ht : EdgeConnected t) {x a : Cell} (ha : a ∈ t)
    (hxa : EdgeAdjacent x a) : EdgeConnected (insert x t) := by
  intro u hu v hv
  rcases Finset.mem_insert.mp hu with rfl | hut
  · rcases Finset.mem_insert.mp hv with rfl | hvt
    · exact Relation.ReflTransGen.refl
    · exact
        (Relation.ReflTransGen.single
          ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ha, hxa⟩).trans
          (edgePath_mono_insert_p (ht a ha v hvt))
  · rcases Finset.mem_insert.mp hv with rfl | hvt
    · exact
        (edgePath_mono_insert_p (ht u hut a ha)).trans
          (Relation.ReflTransGen.single
            ⟨Finset.mem_insert_of_mem ha, Finset.mem_insert_self _ _,
              edgeAdjacent_symm hxa⟩)
    · exact edgePath_mono_insert_p (ht u hut v hvt)

private theorem edgeConnected_tripleLine (a : Cell) :
    EdgeConnected {a, a + (0, 1), a + (0, 2)} := by
  have h01 : EdgeAdjacent a (a + (0, 1)) := by
    right; right; left
    apply Prod.ext <;> dsimp <;> omega
  have h12 : EdgeAdjacent (a + (0, 1)) (a + (0, 2)) := by
    right; right; left
    apply Prod.ext <;> dsimp <;> omega
  have htail : EdgeConnected ({a + (0, 1), a + (0, 2)} : Finset Cell) :=
    edgeConnected_pair h12
  exact edgeConnected_insert_adjacent_p htail (by simp) h01

private theorem pCell_north_edge (a : Cell) (x y : ℤ) :
    EdgeAdjacent (pCell a x y) (pCell a x (y + 1)) := by
  right; right; left
  apply Prod.ext <;> dsimp [pCell] <;> omega

private theorem pCell_east_edge (a : Cell) (x y : ℤ) :
    EdgeAdjacent (pCell a x y) (pCell a (x + 1) y) := by
  left
  apply Prod.ext <;> dsimp [pCell] <;> omega

/-! ## Extracting the marked `P` frame -/

structure PFrame (P : Polyomino) (anchor : Cell) : Prop where
  left_mem : pCell anchor 0 0 ∈ P.cells
  right_mem : pCell anchor 1 0 ∈ P.cells
  southLeft_not : pCell anchor 0 (-1) ∉ P.cells
  southRight_not : pCell anchor 1 (-1) ∉ P.cells
  southeast_not : pCell anchor 2 (-1) ∉ P.cells

theorem pFrame_of_occursAt {P : Polyomino} {anchor : Cell}
    (h : buiPPattern.OccursAt P.cells anchor) : PFrame P anchor := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [pCell] using h.1 (0, 0) (by simp [buiPPattern])
  · simpa [pCell] using h.1 (1, 0) (by simp [buiPPattern])
  · simpa [pCell] using h.2 (0, -1) (by simp [buiPPattern])
  · simpa [pCell] using h.2 (1, -1) (by simp [buiPPattern])
  · simpa [pCell] using h.2 (2, -1) (by simp [buiPPattern])

/-! ## Concrete five-branch seed systems -/

private theorem fin2_ne {i j : Fin 2} (h : i ≠ j) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  fin_cases i <;> fin_cases j <;> simp_all

private theorem fin3_ne {i j : Fin 3} (h : i ≠ j) :
    (i = 0 ∧ (j = 1 ∨ j = 2)) ∨
    (i = 1 ∧ (j = 0 ∨ j = 2)) ∨
    (i = 2 ∧ (j = 0 ∨ j = 1)) := by
  fin_cases i <;> fin_cases j <;> simp_all

private theorem pairSeed_disjoint_leftRight (anchor : Cell)
    (left right : Finset Cell)
    (hl : ∀ c ∈ left, c.1 = anchor.1)
    (hr : ∀ c ∈ right, c.1 = anchor.1 + 1) :
    Disjoint left right := by
  apply Finset.disjoint_left.mpr
  intro c hcl hcr
  have hleft := hl c hcl
  have hright := hr c hcr
  omega

private theorem pFull_top_left_disjoint (P : Polyomino) (anchor : Cell) :
    Disjoint
      (P.cells ∩ {pCell anchor 2 2, pCell anchor (-1) 2,
        pCell anchor 0 2, pCell anchor 1 2})
      (P.cells ∩ {pCell anchor (-1) 1, pCell anchor 0 1,
        pCell anchor 0 0}) := by
  apply Finset.disjoint_left.mpr
  intro c hcTop hcLeft
  have hcTop' := (Finset.mem_inter.mp hcTop).2
  have hcLeft' := (Finset.mem_inter.mp hcLeft).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcTop' hcLeft'
  rcases hcTop' with rfl | rfl | rfl | rfl <;> simp at hcLeft'

private theorem pFull_top_right_disjoint (P : Polyomino) (anchor : Cell) :
    Disjoint
      (P.cells ∩ {pCell anchor 2 2, pCell anchor (-1) 2,
        pCell anchor 0 2, pCell anchor 1 2})
      (P.cells ∩ {pCell anchor 2 1, pCell anchor 1 0,
        pCell anchor 1 1}) := by
  apply Finset.disjoint_left.mpr
  intro c hcTop hcRight
  have hcTop' := (Finset.mem_inter.mp hcTop).2
  have hcRight' := (Finset.mem_inter.mp hcRight).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcTop' hcRight'
  rcases hcTop' with rfl | rfl | rfl | rfl <;> simp at hcRight'

private theorem pFull_left_right_disjoint (P : Polyomino) (anchor : Cell) :
    Disjoint
      (P.cells ∩ {pCell anchor (-1) 1, pCell anchor 0 1,
        pCell anchor 0 0})
      (P.cells ∩ {pCell anchor 2 1, pCell anchor 1 0,
        pCell anchor 1 1}) := by
  apply Finset.disjoint_left.mpr
  intro c hcLeft hcRight
  have hcLeft' := (Finset.mem_inter.mp hcLeft).2
  have hcRight' := (Finset.mem_inter.mp hcRight).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcLeft' hcRight'
  rcases hcLeft' with rfl | rfl | rfl <;> simp at hcRight'

/-- First branch (`E*H`): the cell above the left end is absent.  The optional
upper-right cell is allocated to the `H` seed. -/
def pTopLeftAbsentSeeds {P : Polyomino} {anchor : Cell}
    (frame : PFrame P anchor) (htop : pCell anchor 0 1 ∉ P.cells) :
    PBranchSeeds 2 where
  polyomino := P
  anchor := anchor
  kinds
    | 0 => .e
    | 1 => .h
  seeds
    | 0 => {pCell anchor 0 0}
    | 1 => P.cells ∩ {pCell anchor 1 0, pCell anchor 1 1}
  orientations
    | 0 => GridOrientation.clockwise
    | 1 => GridOrientation.identity
  physicalAnchors
    | 0 => pCell anchor 0 0
    | 1 => pCell anchor 1 0
  seed_subset := by
    intro i c hc
    fin_cases i
    · simpa using (show c = pCell anchor 0 0 from by simpa using hc) ▸ frame.left_mem
    · exact (Finset.mem_inter.mp hc).1
  seed_nonempty := by
    intro i
    fin_cases i
    · simp
    · exact ⟨pCell anchor 1 0,
        Finset.mem_inter.mpr ⟨frame.right_mem, by simp⟩⟩
  seed_connected := by
    intro i
    fin_cases i
    · exact edgeConnected_singleton _
    · by_cases hrightTop : pCell anchor 1 1 ∈ P.cells
      · simpa [frame.right_mem, hrightTop] using
          edgeConnected_pair (pCell_north_edge anchor 1 0)
      · simpa [frame.right_mem, hrightTop] using
          edgeConnected_singleton (pCell anchor 1 0)
  seed_pairwise_disjoint := by
    intro i _ j _ hij
    rcases fin2_ne hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · apply pairSeed_disjoint_leftRight anchor _ _
      · intro c hc
        have hcEq : c = pCell anchor 0 0 := by simpa using hc
        subst c
        simp
      · intro c hc
        have hcSet := (Finset.mem_inter.mp hc).2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcSet
        rcases hcSet with hcEq | hcEq <;> subst c <;> simp
    · apply Disjoint.symm
      apply pairSeed_disjoint_leftRight anchor _ _
      ·
        intro c hc
        have hcEq : c = pCell anchor 0 0 := by simpa using hc
        subst c
        simp
      ·
        intro c hc
        have hcSet := (Finset.mem_inter.mp hc).2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcSet
        rcases hcSet with hcEq | hcEq <;> subst c <;> simp
  index_nonempty := by omega
  physicalAnchor_mem := by
    intro i
    fin_cases i
    · simp
    · simp [frame.right_mem]
  required_mem := by
    intro i offset hoffset
    fin_cases i
    · have : offset = (0, 0) := by simpa [BuiNeighborhood.pattern,
        buiEPattern] using hoffset
      subst offset
      simp
    · have : offset = (0, 0) := by simpa [BuiNeighborhood.pattern,
        buiHPattern] using hoffset
      subst offset
      simp [frame.right_mem]
  forbidden_avoided := by
    intro i offset hoffset
    fin_cases i
    · simp only [BuiNeighborhood.pattern, buiEPattern,
        Finset.mem_insert, Finset.mem_singleton] at hoffset
      rcases hoffset with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (by
          simpa [pCell_add_clockwise_inv, add_offset_eq_pCell] using frame.southLeft_not)
      · exact Or.inl (by simpa [pCell_add_clockwise_inv, add_offset_eq_pCell] using htop)
      · exact Or.inl (by
          simpa [pCell_add_clockwise_inv, add_offset_eq_pCell] using frame.southRight_not)
      · exact Or.inr ⟨1, by decide,
          by simpa [pCell_add_clockwise_inv, add_offset_eq_pCell] using frame.right_mem⟩
      · by_cases hrightTop : pCell anchor 1 1 ∈ P.cells
        · exact Or.inr ⟨1, by decide,
            by simpa [pCell_add_clockwise_inv, add_offset_eq_pCell] using hrightTop⟩
        · exact Or.inl (by simpa [pCell_add_clockwise_inv, add_offset_eq_pCell] using hrightTop)
    · simp only [BuiNeighborhood.pattern, buiHPattern,
        Finset.mem_insert, Finset.mem_singleton] at hoffset
      rcases hoffset with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (by simpa using htop)
      · exact Or.inr ⟨0, by decide, by simp⟩
      · exact Or.inl (by simpa using frame.southLeft_not)
      · exact Or.inl (by simpa using frame.southRight_not)
      · exact Or.inl (by simpa using frame.southeast_not)

/-- Second branch (`Q*D`): the lower-left and upper-left cells form the `Q`
seed, while the lower-right singleton is the `D` seed. -/
def pTopLeftOnlySeeds {P : Polyomino} {anchor : Cell}
    (frame : PFrame P anchor) (h01 : pCell anchor 0 1 ∈ P.cells)
    (h11 : pCell anchor 1 1 ∉ P.cells) : PBranchSeeds 2 where
  polyomino := P
  anchor := anchor
  kinds | 0 => .q | 1 => .d
  seeds | 0 => {pCell anchor 0 0, pCell anchor 0 1}
        | 1 => {pCell anchor 1 0}
  orientations | 0 => GridOrientation.clockwise
               | 1 => GridOrientation.diagonal
  physicalAnchors | 0 => pCell anchor 0 0 | 1 => pCell anchor 1 0
  seed_subset := by
    intro i c hc
    fin_cases i
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact frame.left_mem
      · exact h01
    · simpa using (show c = pCell anchor 1 0 from by simpa using hc) ▸ frame.right_mem
  seed_nonempty := by intro i; fin_cases i <;> simp
  seed_connected := by
    intro i; fin_cases i
    · exact edgeConnected_pair (pCell_north_edge anchor 0 0)
    · exact edgeConnected_singleton _
  seed_pairwise_disjoint := by
    intro i _ j _ hij
    rcases fin2_ne hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact pairSeed_disjoint_leftRight anchor _ _
        (by intro c hc; simp only [Finset.mem_insert, Finset.mem_singleton] at hc;
            rcases hc with rfl | rfl <;> simp [pCell])
        (by
          intro c hc
          have hcEq : c = pCell anchor 1 0 := by simpa using hc
          subst c
          simp)
    · apply Disjoint.symm
      apply pairSeed_disjoint_leftRight anchor _ _
      · intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl <;> simp [pCell]
      · intro c hc
        have hcEq : c = pCell anchor 1 0 := by simpa using hc
        subst c
        simp
  index_nonempty := by omega
  physicalAnchor_mem := by intro i; fin_cases i <;> simp
  required_mem := by
    intro i offset hoffset
    fin_cases i
    · simp only [BuiNeighborhood.pattern, buiQPattern,
        Finset.mem_insert, Finset.mem_singleton] at hoffset
      rcases hoffset with rfl | rfl <;> simp [add_offset_eq_pCell]
    · have : offset = (0, 0) := by simpa [BuiNeighborhood.pattern,
        buiDPattern] using hoffset
      subst offset
      simp
  forbidden_avoided := by
    intro i offset hoffset
    fin_cases i
    · simp only [BuiNeighborhood.pattern, buiQPattern,
        Finset.mem_insert, Finset.mem_singleton] at hoffset
      rcases hoffset with rfl | rfl | rfl | rfl
      · apply Or.inl
        have hcoord :
            pCell anchor 0 0 + GridOrientation.clockwise.inv (-1, 0) =
              pCell anchor 0 (-1) := by
          apply Prod.ext <;> dsimp [pCell, GridOrientation.clockwise] <;> omega
        rw [hcoord]
        exact frame.southLeft_not
      · apply Or.inl
        have hcoord :
            pCell anchor 0 0 + GridOrientation.clockwise.inv (-1, -1) =
              pCell anchor 1 (-1) := by
          apply Prod.ext <;> dsimp [pCell, GridOrientation.clockwise] <;> omega
        rw [hcoord]
        exact frame.southRight_not
      · exact Or.inr ⟨1, by decide, by simp [add_offset_eq_pCell]⟩
      · apply Or.inl
        have hcoord :
            pCell anchor 0 0 + GridOrientation.clockwise.inv (1, -1) =
              pCell anchor 1 1 := by
          apply Prod.ext <;> dsimp [pCell, GridOrientation.clockwise] <;> omega
        rw [hcoord]
        exact h11
    · simp only [BuiNeighborhood.pattern, buiDPattern,
        Finset.mem_insert, Finset.mem_singleton] at hoffset
      rcases hoffset with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (by simpa using frame.southeast_not)
      · exact Or.inl (by simpa using frame.southRight_not)
      · exact Or.inl (by simpa using h11)
      · exact Or.inl (by simpa using frame.southLeft_not)
      · exact Or.inr ⟨0, by decide, by simp⟩
      · exact Or.inr ⟨0, by decide, by simp⟩

/-- Third branch (`X*R`): two vertical domino seeds. -/
def pFirstColumnSeeds {P : Polyomino} {anchor : Cell}
    (frame : PFrame P anchor)
    (h01 : pCell anchor 0 1 ∈ P.cells)
    (h11 : pCell anchor 1 1 ∈ P.cells)
    (h02 : pCell anchor 0 2 ∉ P.cells) : PBranchSeeds 2 where
  polyomino := P
  anchor := anchor
  kinds | 0 => .x | 1 => .r
  seeds | 0 => {pCell anchor 0 1, pCell anchor 0 0}
        | 1 => P.cells ∩
          {pCell anchor 1 0, pCell anchor 1 1, pCell anchor 1 2}
  orientations | 0 => GridOrientation.antiDiagonal
               | 1 => GridOrientation.diagonal
  physicalAnchors | 0 => pCell anchor 0 1 | 1 => pCell anchor 1 0
  seed_subset := by
    intro i c hc
    fin_cases i
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact h01
      · exact frame.left_mem
    · exact (Finset.mem_inter.mp hc).1
  seed_nonempty := by
    intro i
    fin_cases i
    · simp
    · exact ⟨pCell anchor 1 0,
        Finset.mem_inter.mpr ⟨frame.right_mem, by simp⟩⟩
  seed_connected := by
    intro i; fin_cases i
    · exact edgeConnected_pair (edgeAdjacent_symm (pCell_north_edge anchor 0 0))
    · by_cases h12 : pCell anchor 1 2 ∈ P.cells
      · simpa [frame.right_mem, h11, h12, pCell_add] using
          edgeConnected_tripleLine (pCell anchor 1 0)
      · simpa [frame.right_mem, h11, h12] using
          edgeConnected_pair (pCell_north_edge anchor 1 0)
  seed_pairwise_disjoint := by
    intro i _ j _ hij
    rcases fin2_ne hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · apply pairSeed_disjoint_leftRight anchor _ _
      · intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with hcEq | hcEq <;> subst c <;> simp
      · intro c hc
        have hcSet := (Finset.mem_inter.mp hc).2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcSet
        rcases hcSet with hcEq | hcEq | hcEq <;> subst c <;> simp
    · apply Disjoint.symm
      apply pairSeed_disjoint_leftRight anchor _ _
      ·
        intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with hcEq | hcEq <;> subst c <;> simp
      ·
        intro c hc
        have hcSet := (Finset.mem_inter.mp hc).2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcSet
        rcases hcSet with hcEq | hcEq | hcEq <;> subst c <;> simp
  index_nonempty := by omega
  physicalAnchor_mem := by
    intro i; fin_cases i
    · simp
    · simp [frame.right_mem]
  required_mem := by
    intro i offset hoffset
    fin_cases i
    · simp only [BuiNeighborhood.pattern, buiXPattern,
        Finset.mem_insert, Finset.mem_singleton] at hoffset
      rcases hoffset with rfl | rfl <;> simp
    · simp only [BuiNeighborhood.pattern, buiRPattern,
        Finset.mem_insert, Finset.mem_singleton] at hoffset
      rcases hoffset with rfl | rfl <;>
        simp [frame.right_mem, h11]
  forbidden_avoided := by
    intro i offset hoffset
    fin_cases i
    · simp only [BuiNeighborhood.pattern, buiXPattern,
        Finset.mem_insert, Finset.mem_singleton] at hoffset
      rcases hoffset with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (by simpa using h02)
      · exact Or.inl (by simpa using frame.southLeft_not)
      · by_cases h12 : pCell anchor 1 2 ∈ P.cells
        · exact Or.inr ⟨1, by decide, by simp [h12]⟩
        · exact Or.inl (by simpa using h12)
      · exact Or.inr ⟨1, by decide, by simp [h11]⟩
      · exact Or.inr ⟨1, by decide, by simp [frame.right_mem]⟩
      · exact Or.inl (by simpa using frame.southRight_not)
    · simp only [BuiNeighborhood.pattern, buiRPattern,
        Finset.mem_insert, Finset.mem_singleton] at hoffset
      rcases hoffset with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (by simpa using frame.southeast_not)
      · exact Or.inl (by simpa using frame.southRight_not)
      · exact Or.inl (by simpa using frame.southLeft_not)
      · exact Or.inr ⟨0, by decide, by simp⟩
      · exact Or.inr ⟨0, by decide, by simp⟩
      · exact Or.inl (by simpa using h02)

/-- Fourth branch (`V*Y`): a vertical triple on the left and a vertical domino
on the right. -/
def pFirstColumnTopRightSeeds {P : Polyomino} {anchor : Cell}
    (frame : PFrame P anchor)
    (h01 : pCell anchor 0 1 ∈ P.cells)
    (h02 : pCell anchor 0 2 ∈ P.cells)
    (h11 : pCell anchor 1 1 ∈ P.cells)
    (h12 : pCell anchor 1 2 ∉ P.cells) : PBranchSeeds 2 where
  polyomino := P
  anchor := anchor
  kinds | 0 => .v | 1 => .y
  seeds | 0 => {pCell anchor 0 0, pCell anchor 0 1, pCell anchor 0 2}
        | 1 => {pCell anchor 1 0, pCell anchor 1 1}
  orientations | 0 => GridOrientation.clockwise
               | 1 => GridOrientation.diagonal
  physicalAnchors | 0 => pCell anchor 0 0 | 1 => pCell anchor 1 0
  seed_subset := by
    intro i c hc
    fin_cases i
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl
      · exact frame.left_mem
      · exact h01
      · exact h02
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact frame.right_mem
      · exact h11
  seed_nonempty := by intro i; fin_cases i <;> simp
  seed_connected := by
    intro i; fin_cases i
    · simpa [pCell_add, add_offset_eq_pCell] using
        edgeConnected_tripleLine (pCell anchor 0 0)
    · exact edgeConnected_pair (pCell_north_edge anchor 1 0)
  seed_pairwise_disjoint := by
    intro i _ j _ hij
    rcases fin2_ne hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · apply pairSeed_disjoint_leftRight anchor _ _
      · intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with hcEq | hcEq | hcEq <;> subst c <;> simp
      · intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with hcEq | hcEq <;> subst c <;> simp
    · apply Disjoint.symm
      apply pairSeed_disjoint_leftRight anchor _ _
      ·
        intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with hcEq | hcEq | hcEq <;> subst c <;> simp
      ·
        intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with hcEq | hcEq <;> subst c <;> simp
  index_nonempty := by omega
  physicalAnchor_mem := by intro i; fin_cases i <;> simp
  required_mem := by
    intro i offset hoffset
    fin_cases i
    · simp only [BuiNeighborhood.pattern, buiVPattern,
        Finset.mem_insert, Finset.mem_singleton] at hoffset
      rcases hoffset with rfl | rfl | rfl <;>
        simp [add_offset_eq_pCell]
    · simp only [BuiNeighborhood.pattern, buiYPattern,
        Finset.mem_insert, Finset.mem_singleton] at hoffset
      rcases hoffset with rfl | rfl <;> simp
  forbidden_avoided := by
    intro i offset hoffset
    fin_cases i
    · simp only [BuiNeighborhood.pattern, buiVPattern,
        Finset.mem_insert, Finset.mem_singleton] at hoffset
      rcases hoffset with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (by
          simpa [pCell_add_clockwise_inv, add_offset_eq_pCell] using frame.southLeft_not)
      · exact Or.inl (by
          simpa [pCell_add_clockwise_inv, add_offset_eq_pCell] using frame.southRight_not)
      · exact Or.inr ⟨1, by decide, by simp [add_offset_eq_pCell]⟩
      · exact Or.inr ⟨1, by decide, by simp [add_offset_eq_pCell]⟩
      · exact Or.inl (by simpa [pCell_add_clockwise_inv, add_offset_eq_pCell] using h12)
    · simp only [BuiNeighborhood.pattern, buiYPattern,
        Finset.mem_insert, Finset.mem_singleton] at hoffset
      rcases hoffset with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (by simpa using frame.southeast_not)
      · exact Or.inl (by simpa using frame.southRight_not)
      · exact Or.inl (by simpa using h12)
      · exact Or.inl (by simpa using frame.southLeft_not)
      · exact Or.inr ⟨0, by decide, by simp⟩
      · exact Or.inr ⟨0, by decide, by simp⟩
      · exact Or.inr ⟨0, by decide, by simp⟩

/-- Fifth branch (`U*Y*Z`): the full two-by-three rectangle is split into its
top horizontal domino and its two lower vertical dominoes. -/
def pFullRectangleSeeds {P : Polyomino} {anchor : Cell}
    (frame : PFrame P anchor)
    (h01 : pCell anchor 0 1 ∈ P.cells)
    (h02 : pCell anchor 0 2 ∈ P.cells)
    (h11 : pCell anchor 1 1 ∈ P.cells)
    (h12 : pCell anchor 1 2 ∈ P.cells) : PBranchSeeds 3 where
  polyomino := P
  anchor := anchor
  kinds | 0 => .u | 1 => .y | 2 => .z
  seeds | 0 => P.cells ∩
          {pCell anchor 2 2, pCell anchor (-1) 2,
            pCell anchor 0 2, pCell anchor 1 2}
        | 1 => P.cells ∩
          {pCell anchor (-1) 1, pCell anchor 0 1, pCell anchor 0 0}
        | 2 => P.cells ∩
          {pCell anchor 2 1, pCell anchor 1 0, pCell anchor 1 1}
  orientations | 0 => GridOrientation.identity
               | 1 => GridOrientation.antiDiagonal
               | 2 => GridOrientation.diagonal
  physicalAnchors | 0 => pCell anchor 0 2
                  | 1 => pCell anchor 0 1
                  | 2 => pCell anchor 1 0
  seed_subset := by
    intro i c hc
    fin_cases i <;> exact (Finset.mem_inter.mp hc).1
  seed_nonempty := by
    intro i
    fin_cases i
    · exact ⟨pCell anchor 0 2, Finset.mem_inter.mpr
        ⟨h02, by simp⟩⟩
    · exact ⟨pCell anchor 0 1, Finset.mem_inter.mpr
        ⟨h01, by simp⟩⟩
    · exact ⟨pCell anchor 1 0, Finset.mem_inter.mpr
        ⟨frame.right_mem, by simp⟩⟩
  seed_connected := by
    intro i
    fin_cases i
    · by_cases hleft : pCell anchor (-1) 2 ∈ P.cells
      · by_cases hright : pCell anchor 2 2 ∈ P.cells
        · have hbase := edgeConnected_pair (pCell_east_edge anchor 0 2)
          have hwithLeft := edgeConnected_insert_adjacent_p hbase
            (by simp : pCell anchor 0 2 ∈
              ({pCell anchor 0 2, pCell anchor 1 2} : Finset Cell))
            (pCell_east_edge anchor (-1) 2)
          have hboth := edgeConnected_insert_adjacent_p hwithLeft
            (by simp : pCell anchor 1 2 ∈
              insert (pCell anchor (-1) 2)
                ({pCell anchor 0 2, pCell anchor 1 2} : Finset Cell))
            (edgeAdjacent_symm (pCell_east_edge anchor 1 2))
          simpa [hleft, hright, h02, h12] using hboth
        · have hbase := edgeConnected_pair (pCell_east_edge anchor 0 2)
          have hwithLeft := edgeConnected_insert_adjacent_p hbase
            (by simp : pCell anchor 0 2 ∈
              ({pCell anchor 0 2, pCell anchor 1 2} : Finset Cell))
            (pCell_east_edge anchor (-1) 2)
          simpa [hleft, hright, h02, h12] using hwithLeft
      · by_cases hright : pCell anchor 2 2 ∈ P.cells
        · have hbase := edgeConnected_pair (pCell_east_edge anchor 0 2)
          have hwithRight := edgeConnected_insert_adjacent_p hbase
            (by simp : pCell anchor 1 2 ∈
              ({pCell anchor 0 2, pCell anchor 1 2} : Finset Cell))
            (edgeAdjacent_symm (pCell_east_edge anchor 1 2))
          simpa [hleft, hright, h02, h12] using hwithRight
        · simpa [hleft, hright, h02, h12] using
            edgeConnected_pair (pCell_east_edge anchor 0 2)
    · by_cases hleft : pCell anchor (-1) 1 ∈ P.cells
      · have hbase := edgeConnected_pair
            (edgeAdjacent_symm (pCell_north_edge anchor 0 0))
        have hwithLeft := edgeConnected_insert_adjacent_p hbase
          (by simp : pCell anchor 0 1 ∈
            ({pCell anchor 0 1, pCell anchor 0 0} : Finset Cell))
          (pCell_east_edge anchor (-1) 1)
        have h00 : pCell anchor 0 0 ∈ P.cells := frame.left_mem
        have hanchor : anchor ∈ P.cells := by
          simpa only [pCell_zero] using h00
        have hseed :
            P.cells ∩
                {pCell anchor (-1) 1, pCell anchor 0 1,
                  pCell anchor 0 0} =
              {pCell anchor (-1) 1, pCell anchor 0 1,
                pCell anchor 0 0} := by
          ext c
          simp [hleft, h01, hanchor]
        rw [hseed]
        exact hwithLeft
      · have h00 : pCell anchor 0 0 ∈ P.cells := frame.left_mem
        have hanchor : anchor ∈ P.cells := by
          simpa only [pCell_zero] using h00
        have hseed :
            P.cells ∩
                {pCell anchor (-1) 1, pCell anchor 0 1,
                  pCell anchor 0 0} =
              {pCell anchor 0 1, pCell anchor 0 0} := by
          ext c
          simp [hleft, h01, hanchor]
        rw [hseed]
        exact edgeConnected_pair
          (edgeAdjacent_symm (pCell_north_edge anchor 0 0))
    · by_cases hright : pCell anchor 2 1 ∈ P.cells
      · have hbase := edgeConnected_pair (pCell_north_edge anchor 1 0)
        have hwithRight := edgeConnected_insert_adjacent_p hbase
          (by simp : pCell anchor 1 1 ∈
            ({pCell anchor 1 0, pCell anchor 1 1} : Finset Cell))
          (edgeAdjacent_symm (pCell_east_edge anchor 1 1))
        simpa [hright, frame.right_mem, h11] using hwithRight
      · simpa [hright, frame.right_mem, h11] using
          edgeConnected_pair (pCell_north_edge anchor 1 0)
  seed_pairwise_disjoint := by
    intro i _ j _ hij
    rcases fin3_ne hij with
      ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩
    · exact pFull_top_left_disjoint P anchor
    · exact pFull_top_right_disjoint P anchor
    · exact (pFull_top_left_disjoint P anchor).symm
    · exact pFull_left_right_disjoint P anchor
    · exact (pFull_top_right_disjoint P anchor).symm
    · exact (pFull_left_right_disjoint P anchor).symm
  index_nonempty := by omega
  physicalAnchor_mem := by
    intro i
    fin_cases i
    · simp [h02]
    · simp [h01]
    · simp [frame.right_mem]
  required_mem := by
    have hanchor : anchor ∈ P.cells := by
      simpa only [pCell_zero] using frame.left_mem
    intro i offset hoffset
    fin_cases i
    · simp only [BuiNeighborhood.pattern, buiUPattern,
        Finset.mem_insert, Finset.mem_singleton] at hoffset
      rcases hoffset with rfl | rfl <;>
        simp [h02, h12]
    · simp only [BuiNeighborhood.pattern, buiYPattern,
        Finset.mem_insert, Finset.mem_singleton] at hoffset
      rcases hoffset with rfl | rfl <;>
        simp [h01, hanchor]
    · simp only [BuiNeighborhood.pattern, buiZPattern,
        Finset.mem_insert, Finset.mem_singleton] at hoffset
      rcases hoffset with rfl | rfl <;>
        simp [frame.right_mem, h11]
  forbidden_avoided := by
    have hanchor : anchor ∈ P.cells := by
      simpa only [pCell_zero] using frame.left_mem
    intro i offset hoffset
    fin_cases i
    · simp only [BuiNeighborhood.pattern, buiUPattern,
        Finset.mem_insert, Finset.mem_singleton] at hoffset
      rcases hoffset with rfl | rfl | rfl | rfl
      · by_cases hleft : pCell anchor (-1) 1 ∈ P.cells
        · exact Or.inr ⟨1, by decide, by simp [hleft]⟩
        · exact Or.inl (by simpa using hleft)
      · exact Or.inr ⟨1, by decide, by simp [h01]⟩
      · exact Or.inr ⟨2, by decide, by simp [h11]⟩
      · by_cases hright : pCell anchor 2 1 ∈ P.cells
        · exact Or.inr ⟨2, by decide, by simp [hright]⟩
        · exact Or.inl (by simpa using hright)
    · simp only [BuiNeighborhood.pattern, buiYPattern,
        Finset.mem_insert, Finset.mem_singleton] at hoffset
      rcases hoffset with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · by_cases hleft : pCell anchor (-1) 2 ∈ P.cells
        · exact Or.inr ⟨0, by decide, by simp [hleft]⟩
        · exact Or.inl (by simpa using hleft)
      · exact Or.inr ⟨0, by decide, by simp [h02]⟩
      · exact Or.inl (by simpa using frame.southLeft_not)
      · exact Or.inr ⟨0, by decide, by simp [h12]⟩
      · exact Or.inr ⟨2, by decide, by simp [h11]⟩
      · exact Or.inr ⟨2, by decide, by simp [frame.right_mem]⟩
      · exact Or.inl (by simpa using frame.southRight_not)
    · simp only [BuiNeighborhood.pattern, buiZPattern,
        Finset.mem_insert, Finset.mem_singleton] at hoffset
      rcases hoffset with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (by simpa using frame.southeast_not)
      · by_cases hright : pCell anchor 2 2 ∈ P.cells
        · exact Or.inr ⟨0, by decide, by simp [hright]⟩
        · exact Or.inl (by simpa using hright)
      · exact Or.inl (by simpa using frame.southRight_not)
      · exact Or.inr ⟨0, by decide, by simp [h12]⟩
      · exact Or.inl (by simpa using frame.southLeft_not)
      · exact Or.inr ⟨1, by decide, by simp [hanchor]⟩
      · exact Or.inr ⟨1, by decide, by simp [h01]⟩
      · exact Or.inr ⟨0, by decide, by simp [h02]⟩

/-! ## Exhaustiveness of the local decomposition -/

/-- A two-territory branch datum with fixed source, anchor, and advertised
ordered target types. -/
def IsPTwoBranchData (P : Polyomino) (anchor : Cell)
    (left right : BuiNeighborhood) (D : PBranchSeeds 2) : Prop :=
  D.polyomino = P ∧ D.anchor = anchor ∧
    D.kinds 0 = left ∧ D.kinds 1 = right

/-- A three-territory branch datum with fixed source, anchor, and advertised
ordered target types. -/
def IsPThreeBranchData (P : Polyomino) (anchor : Cell)
    (first second third : BuiNeighborhood) (D : PBranchSeeds 3) : Prop :=
  D.polyomino = P ∧ D.anchor = anchor ∧
    D.kinds 0 = first ∧ D.kinds 1 = second ∧ D.kinds 2 = third

/-- Every marked `P` occurrence of size at least two enters one of the five
advertised product branches.  In the first branch, the optional upper-right
cell is allocated to the `H` seed. -/
theorem exists_pBranchSeeds {P : Polyomino} {anchor : Cell}
    (hoccurs : buiPPattern.OccursAt P.cells anchor)
    (_hcard : 2 ≤ P.cells.card) :
    (∃ D : PBranchSeeds 2, IsPTwoBranchData P anchor .e .h D) ∨
    (∃ D : PBranchSeeds 2, IsPTwoBranchData P anchor .q .d D) ∨
    (∃ D : PBranchSeeds 2, IsPTwoBranchData P anchor .x .r D) ∨
    (∃ D : PBranchSeeds 2, IsPTwoBranchData P anchor .v .y D) ∨
    (∃ D : PBranchSeeds 3, IsPThreeBranchData P anchor .u .y .z D) := by
  let frame := pFrame_of_occursAt hoccurs
  rcases pBranchAt_cases P.cells anchor with
    hfirst | hsecond | hthird | hfourth | hfifth
  · rcases hfirst with ⟨_branch, h01⟩
    exact Or.inl ⟨pTopLeftAbsentSeeds frame h01, rfl, rfl, rfl, rfl⟩
  · rcases hsecond with ⟨_branch, h01, h11⟩
    exact Or.inr <| Or.inl
      ⟨pTopLeftOnlySeeds frame h01 h11, rfl, rfl, rfl, rfl⟩
  · rcases hthird with ⟨_branch, h01, h11, h02⟩
    exact Or.inr <| Or.inr <| Or.inl
      ⟨pFirstColumnSeeds frame h01 h11 h02, rfl, rfl, rfl, rfl⟩
  · rcases hfourth with ⟨_branch, h01, h02, h11, h12⟩
    exact Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨pFirstColumnTopRightSeeds frame h01 h02 h11 h12,
        rfl, rfl, rfl, rfl⟩
  · rcases hfifth with ⟨_branch, h01, h02, h11, h12⟩
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr
      ⟨pFullRectangleSeeds frame h01 h02 h11 h12,
        rfl, rfl, rfl, rfl, rfl⟩

/-! ## Explicit branch outputs -/

/-- The two normalized marked occurrences in any two-territory branch. -/
noncomputable def PBranchSeeds.twoOutput (D : PBranchSeeds 2) :
    MarkedOccurrence (D.kinds 0) (D.partition.territories 0).card ×
    MarkedOccurrence (D.kinds 1) (D.partition.territories 1).card :=
  ((D.territoryOccurrence 0).toMarkedOccurrence,
    (D.territoryOccurrence 1).toMarkedOccurrence)

/-- The three normalized marked occurrences in the full-rectangle branch. -/
noncomputable def PBranchSeeds.threeOutput (D : PBranchSeeds 3) :
    MarkedOccurrence (D.kinds 0) (D.partition.territories 0).card ×
    MarkedOccurrence (D.kinds 1) (D.partition.territories 1).card ×
    MarkedOccurrence (D.kinds 2) (D.partition.territories 2).card :=
  ((D.territoryOccurrence 0).toMarkedOccurrence,
    (D.territoryOccurrence 1).toMarkedOccurrence,
    (D.territoryOccurrence 2).toMarkedOccurrence)

/-- Each two-territory output has positive indices adding to the source size. -/
theorem PBranchSeeds.twoOutput_indices (D : PBranchSeeds 2) :
    0 < (D.partition.territories 0).card ∧
    0 < (D.partition.territories 1).card ∧
    (D.partition.territories 0).card +
      (D.partition.territories 1).card = D.polyomino.cells.card := by
  refine ⟨Finset.card_pos.mpr (D.partition.territory_nonempty 0),
    Finset.card_pos.mpr (D.partition.territory_nonempty 1), ?_⟩
  simpa only [Fin.sum_univ_two] using D.partition_card_sum

/-- Each three-territory output has positive indices adding to the source
size, exactly matching the support of the positive three-fold convolution. -/
theorem PBranchSeeds.threeOutput_indices (D : PBranchSeeds 3) :
    0 < (D.partition.territories 0).card ∧
    0 < (D.partition.territories 1).card ∧
    0 < (D.partition.territories 2).card ∧
    (D.partition.territories 0).card +
      (D.partition.territories 1).card +
      (D.partition.territories 2).card = D.polyomino.cells.card := by
  refine ⟨Finset.card_pos.mpr (D.partition.territory_nonempty 0),
    Finset.card_pos.mpr (D.partition.territory_nonempty 1),
    Finset.card_pos.mpr (D.partition.territory_nonempty 2), ?_⟩
  have h := D.partition_card_sum
  rw [Fin.sum_univ_succ, Fin.sum_univ_two] at h
  simpa [add_assoc] using h

end LeanProofs.KlarnerConstant
