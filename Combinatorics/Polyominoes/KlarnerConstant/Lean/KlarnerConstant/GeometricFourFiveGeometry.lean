import KlarnerConstant.GeometricFourFiveGeometryCore

/-!
# Target-pattern geometry for the five-branch `S` recurrence

This module builds the erasure wrappers, transformed boundary occurrences,
and the five branch maps used by the endpoint injection.
-/

namespace LeanProofs.KlarnerConstant

namespace GeometricFourFiveInternal

def eraseLeafPolyomino (P : Polyomino) (leaf parent : Cell)
    (hleaf : leaf ∈ P.cells) (hparent : parent ∈ P.cells)
    (hne : leaf ≠ parent)
    (honly : ∀ {c}, c ∈ P.cells → EdgeAdjacent leaf c → c = parent) :
    Polyomino where
  cells := P.cells.erase leaf
  nonempty := ⟨parent, Finset.mem_erase.mpr ⟨hne.symm, hparent⟩⟩
  edgeConnected := edgeConnected_eraseLeaf P leaf parent hleaf hparent hne honly

@[simp] theorem eraseLeafPolyomino_cells (P : Polyomino) (leaf parent : Cell)
    (hleaf : leaf ∈ P.cells) (hparent : parent ∈ P.cells)
    (hne : leaf ≠ parent)
    (honly : ∀ {c}, c ∈ P.cells → EdgeAdjacent leaf c → c = parent) :
    (eraseLeafPolyomino P leaf parent hleaf hparent hne honly).cells =
      P.cells.erase leaf := rfl

def eraseLowerDominoPolyomino (P : Polyomino)
    (a b u v : Cell) (ha : a ∈ P.cells) (hb : b ∈ P.cells)
    (hu : u ∈ P.cells) (hv : v ∈ P.cells)
    (hab : a ≠ b) (hau : a ≠ u) (hub : u ≠ b)
    (hva : v ≠ a) (hbv : b ≠ v)
    (huv : EdgeAdjacent u v)
    (haNeighbors : ∀ {c}, c ∈ P.cells → EdgeAdjacent a c →
      c = b ∨ c = u)
    (hbNeighbors : ∀ {c}, c ∈ P.cells → EdgeAdjacent b c →
      c = a ∨ c = v) : Polyomino where
  cells := (P.cells.erase a).erase b
  nonempty := ⟨u, Finset.mem_erase.mpr ⟨hub,
    Finset.mem_erase.mpr ⟨hau.symm, hu⟩⟩⟩
  edgeConnected := edgeConnected_eraseLowerDomino P a b u v ha hb hu hv
    hab hau hub hva hbv huv haNeighbors hbNeighbors

@[simp] theorem eraseLowerDominoPolyomino_cells (P : Polyomino)
    (a b u v : Cell) (ha : a ∈ P.cells) (hb : b ∈ P.cells)
    (hu : u ∈ P.cells) (hv : v ∈ P.cells)
    (hab : a ≠ b) (hau : a ≠ u) (hub : u ≠ b)
    (hva : v ≠ a) (hbv : b ≠ v)
    (huv : EdgeAdjacent u v)
    (haNeighbors : ∀ {c}, c ∈ P.cells → EdgeAdjacent a c →
      c = b ∨ c = u)
    (hbNeighbors : ∀ {c}, c ∈ P.cells → EdgeAdjacent b c →
      c = a ∨ c = v) :
    (eraseLowerDominoPolyomino P a b u v ha hb hu hv hab hau hub hva hbv huv
      haNeighbors hbNeighbors).cells = (P.cells.erase a).erase b := rfl

theorem bool_partition_card {D : SeedSystem Bool}
    (part : SeededPartition D) :
    (part.territories false).card + (part.territories true).card =
      D.cells.card := by
  have hdisjoint := part.territory_pairwise_disjoint false true (by decide)
  rw [← Finset.card_union_of_disjoint hdisjoint]
  have hcover : part.territories false ∪ part.territories true = D.cells := by
    rw [← part.cover]
    ext c
    simp [coveredCells, or_comm]
  rw [hcover]

theorem erase_one_card {n : ℕ} (P : NormalizedPolyomino n)
    {a : Cell} (ha : a ∈ P.toPolyomino.cells) :
    (P.toPolyomino.cells.erase a).card = n - 1 := by
  rw [Finset.card_erase_of_mem ha, P.card_cells]

theorem erase_two_card {n : ℕ} (P : NormalizedPolyomino n)
    {a b : Cell} (ha : a ∈ P.toPolyomino.cells)
    (hb : b ∈ P.toPolyomino.cells) (hab : a ≠ b) :
    ((P.toPolyomino.cells.erase a).erase b).card = n - 2 := by
  rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, hb⟩),
    Finset.card_erase_of_mem ha, P.card_cells]
  omega

theorem sdiff_pair_eq_erase_erase (cells : Finset Cell) (a b : Cell) :
    cells \ {a, b} = (cells.erase a).erase b := by
  ext c
  simp [and_comm, and_left_comm, and_assoc]

/-! ## Exposed patterns on the five branch remainders -/

theorem transform_mem (sigma : GridSymmetry) (P : Polyomino)
    {c : Cell} (hc : c ∈ P.cells) :
    sigma.equiv c ∈ (sigma.transformPolyomino P).cells := by
  exact Finset.mem_image.mpr ⟨c, hc, rfl⟩

theorem transform_not_mem (sigma : GridSymmetry) (P : Polyomino)
    {c : Cell} (hc : c ∉ P.cells) :
    sigma.equiv c ∉ (sigma.transformPolyomino P).cells := by
  intro h
  exact hc (sigma.mem_transformCells.mp h)

theorem territory_not_mem_of_not_ambient {D : SeedSystem Bool}
    (part : SeededPartition D) (i : Bool) {c : Cell} (hc : c ∉ D.cells) :
    c ∉ part.territories i :=
  fun h => hc (part.territory_subset i h)

theorem territory_not_mem_of_other_seed {D : SeedSystem Bool}
    (part : SeededPartition D) (i j : Bool) (hij : i ≠ j)
    {c : Cell} (hc : c ∈ D.seeds j) : c ∉ part.territories i := by
  intro hterritory
  exact (Finset.disjoint_left.mp (part.disjoint_foreign_seed hij)) hterritory hc

def sFirstRemainder {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∉ x.1.toPolyomino.cells) : Polyomino :=
  eraseLeafPolyomino x.1.toPolyomino (sA x.2.1) (sB x.2.1)
    (by simpa [sA] using frame.a_mem)
    (by simpa [sB] using frame.b_mem)
    (sA_ne_sB x.2.1)
    (by
      intro c hc hadj
      rcases s_a_neighbors frame hc hadj with h | h
      · exact h
      · exact (hu (h ▸ hc)).elim)

theorem sFirst_g_occursAt {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∉ x.1.toPolyomino.cells) :
    buiGPattern.OccursAt
      (diagonalSymmetry.transformPolyomino (sFirstRemainder x frame hu)).cells
      (diagonalSymmetry.equiv (sB x.2.1)) := by
  let R := sFirstRemainder x frame hu
  constructor
  · intro offset hoff
    have hoff' : offset = (0, 0) := by simpa [buiGPattern] using hoff
    subst offset
    rw [show diagonalSymmetry.equiv (sB x.2.1) + (0, 0) =
        diagonalSymmetry.equiv (sB x.2.1) by simp]
    apply transform_mem
    exact Finset.mem_erase.mpr ⟨(sA_ne_sB x.2.1).symm,
      by simpa [sB] using frame.b_mem⟩
  · intro offset hoff
    simp only [buiGPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h <;> subst offset
    · rw [show diagonalSymmetry.equiv (sB x.2.1) + (-1, 0) =
          diagonalSymmetry.equiv (cellAt x.2.1 1 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, sB, cellAt] <;> omega]
      apply transform_not_mem
      exact fun hm => frame.southeast_not_mem (Finset.mem_erase.mp hm).2
    · rw [show diagonalSymmetry.equiv (sB x.2.1) + (-1, -1) =
          diagonalSymmetry.equiv (cellAt x.2.1 0 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, sB, cellAt] <;> omega]
      apply transform_not_mem
      exact fun hm => frame.south_not_mem (Finset.mem_erase.mp hm).2
    · rw [show diagonalSymmetry.equiv (sB x.2.1) + (0, -1) =
          diagonalSymmetry.equiv (sA x.2.1) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, sA, sB, cellAt] <;> omega]
      apply transform_not_mem
      exact fun hm => (Finset.mem_erase.mp hm).1 rfl
    · rw [show diagonalSymmetry.equiv (sB x.2.1) + (1, -1) =
          diagonalSymmetry.equiv (sU x.2.1) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, sB, sU, cellAt] <;> omega]
      apply transform_not_mem
      exact fun hm => hu (Finset.mem_erase.mp hm).2

theorem sSecond_left_e_occursAt {n : ℕ}
    (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∉ x.1.toPolyomino.cells)
    (part : SeededPartition (sSecondSystem x frame hu)) :
    buiEPattern.OccursAt (part.territoryPolyomino false).cells (sU x.2.1) := by
  constructor
  · intro offset hoff
    have : offset = (0, 0) := by simpa [buiEPattern] using hoff
    subst offset
    rw [sU_add_offset]
    norm_num
    change sU x.2.1 ∈ _
    exact part.seed_subset false (by
      rw [sSecondSystem_seeds]
      simp [sSecondSeeds])
  · intro offset hoff
    simp only [buiEPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h | h <;> subst offset
    · rw [sU_add_offset]
      norm_num
      apply territory_not_mem_of_not_ambient part false
      rw [sSecondSystem_cells]
      intro hm
      exact frame.leftNorth_not_mem (Finset.mem_sdiff.mp hm).1
    · rw [sU_add_offset]
      norm_num
      change sV x.2.1 ∉ _
      apply territory_not_mem_of_not_ambient part false
      rw [sSecondSystem_cells]
      intro hm
      exact hv (Finset.mem_sdiff.mp hm).1
    · rw [sU_add_offset]
      norm_num
      apply territory_not_mem_of_not_ambient part false
      rw [sSecondSystem_cells]
      intro hm
      exact frame.left_not_mem (Finset.mem_sdiff.mp hm).1
    · rw [sU_add_offset]
      norm_num
      change sA x.2.1 ∉ _
      apply territory_not_mem_of_not_ambient part false
      rw [sSecondSystem_cells]
      simp
    · rw [sU_add_offset]
      norm_num
      change sB x.2.1 ∉ _
      apply territory_not_mem_of_other_seed part false true (by decide)
      rw [sSecondSystem_seeds]
      simp [sSecondSeeds]

theorem sSecond_right_e_occursAt {n : ℕ}
    (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∉ x.1.toPolyomino.cells)
    (part : SeededPartition (sSecondSystem x frame hu)) :
    buiEPattern.OccursAt
      (diagonalSymmetry.transformPolyomino (part.territoryPolyomino true)).cells
      (diagonalSymmetry.equiv (sB x.2.1)) := by
  constructor
  · intro offset hoff
    have : offset = (0, 0) := by simpa [buiEPattern] using hoff
    subst offset
    rw [show ((0, 0) : Cell) = 0 by rfl, add_zero]
    exact transform_mem diagonalSymmetry (part.territoryPolyomino true)
      (part.seed_subset true (show sB x.2.1 ∈
          (sSecondSystem x frame hu).seeds true from by
        rw [sSecondSystem_seeds]
        simp [sSecondSeeds]))
  · intro offset hoff
    simp only [buiEPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h | h <;> subst offset
    · rw [show diagonalSymmetry.equiv (sB x.2.1) + (-1, 0) =
          diagonalSymmetry.equiv (cellAt x.2.1 1 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, sB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [sSecondSystem_cells]
      intro hm
      exact frame.southeast_not_mem (Finset.mem_sdiff.mp hm).1
    · rw [show diagonalSymmetry.equiv (sB x.2.1) + (1, 0) =
          diagonalSymmetry.equiv (sV x.2.1) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, sB, sV, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [sSecondSystem_cells]
      intro hm
      exact hv (Finset.mem_sdiff.mp hm).1
    · rw [show diagonalSymmetry.equiv (sB x.2.1) + (-1, -1) =
          diagonalSymmetry.equiv (cellAt x.2.1 0 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, sB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [sSecondSystem_cells]
      intro hm
      exact frame.south_not_mem (Finset.mem_sdiff.mp hm).1
    · rw [show diagonalSymmetry.equiv (sB x.2.1) + (0, -1) =
          diagonalSymmetry.equiv (sA x.2.1) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, sA, sB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [sSecondSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    · rw [show diagonalSymmetry.equiv (sB x.2.1) + (1, -1) =
          diagonalSymmetry.equiv (sU x.2.1) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, sB, sU, cellAt] <;> omega]
      apply transform_not_mem
      exact territory_not_mem_of_other_seed part true false (by decide)
        (by rw [sSecondSystem_seeds]; simp [sSecondSeeds])

def sThirdRemainder {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∉ x.1.toPolyomino.cells) : Polyomino :=
  eraseLowerDominoPolyomino x.1.toPolyomino
    (sA x.2.1) (sB x.2.1) (sU x.2.1) (sV x.2.1)
    (by simpa [sA] using frame.a_mem) (by simpa [sB] using frame.b_mem)
    hu hv (sA_ne_sB _) (sA_ne_sU _) (sU_ne_sB _)
    ((sA_ne_sV _).symm) (sB_ne_sV _)
    (by simpa [sU, sV] using cellAt_east x.2.1 0 1)
    (s_a_neighbors frame) (s_b_neighbors_of_r_absent frame hr)

theorem sThird_u_mem {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∉ x.1.toPolyomino.cells) :
    sU x.2.1 ∈ (sThirdRemainder x frame hu hv hr).cells := by
  exact Finset.mem_erase.mpr ⟨sU_ne_sB x.2.1,
    Finset.mem_erase.mpr ⟨(sA_ne_sU x.2.1).symm, hu⟩⟩

theorem sThird_t_occursAt {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∉ x.1.toPolyomino.cells) :
    buiTPattern.OccursAt (sThirdRemainder x frame hu hv hr).cells (sU x.2.1) := by
  constructor
  · intro offset hoffset
    simp only [buiTPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with rfl | rfl
    · rw [sU_add_offset]
      norm_num
      exact sThird_u_mem x frame hu hv hr
    · rw [sU_add_offset]
      norm_num
      change sV x.2.1 ∈ _
      exact Finset.mem_erase.mpr ⟨(sB_ne_sV x.2.1).symm,
        Finset.mem_erase.mpr ⟨(sA_ne_sV x.2.1).symm, hv⟩⟩
  · intro offset hoffset
    simp only [buiTPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with h | h | h | h | h <;> subst offset
    · rw [sU_add_offset]
      norm_num
      intro hm
      exact frame.leftNorth_not_mem
        (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).2
    · rw [sU_add_offset]
      norm_num
      intro hm
      exact frame.left_not_mem
        (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).2
    · rw [sU_add_offset]
      norm_num
      change sA x.2.1 ∉ _
      intro hm
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1 rfl
    · rw [sU_add_offset]
      norm_num
      change sB x.2.1 ∉ _
      intro hm
      exact (Finset.mem_erase.mp hm).1 rfl
    · rw [sU_add_offset]
      norm_num
      change sR x.2.1 ∉ _
      intro hm
      exact hr (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).2

theorem sFourth_left_x_occursAt {n : ℕ}
    (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : sS x.2.1 ∉ x.1.toPolyomino.cells)
    (part : SeededPartition (sFourthSystem x frame hu hv hr)) :
    buiXPattern.OccursAt (part.territoryPolyomino false).cells (sU x.2.1) := by
  constructor
  · intro offset hoffset
    simp only [buiXPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with rfl | rfl
    · rw [sU_add_offset]
      norm_num
      change sU x.2.1 ∈ _
      exact part.seed_subset false (by
        rw [sFourthSystem_seeds]
        simp [sFourthSeeds])
    · rw [sU_add_offset]
      norm_num
      change sV x.2.1 ∈ _
      exact part.seed_subset false (by
        rw [sFourthSystem_seeds]
        simp [sFourthSeeds])
  · intro offset hoffset
    simp only [buiXPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with h | h | h | h | h | h <;> subst offset
    · rw [sU_add_offset]
      norm_num
      apply territory_not_mem_of_not_ambient part false
      rw [sFourthSystem_cells]
      intro hm
      exact frame.leftNorth_not_mem (Finset.mem_sdiff.mp hm).1
    · rw [sU_add_offset]
      norm_num
      change sS x.2.1 ∉ _
      apply territory_not_mem_of_not_ambient part false
      rw [sFourthSystem_cells]
      intro hm
      exact hs (Finset.mem_sdiff.mp hm).1
    · rw [sU_add_offset]
      norm_num
      apply territory_not_mem_of_not_ambient part false
      rw [sFourthSystem_cells]
      intro hm
      exact frame.left_not_mem (Finset.mem_sdiff.mp hm).1
    · rw [sU_add_offset]
      norm_num
      change sA x.2.1 ∉ _
      apply territory_not_mem_of_not_ambient part false
      rw [sFourthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    · rw [sU_add_offset]
      norm_num
      change sB x.2.1 ∉ _
      apply territory_not_mem_of_not_ambient part false
      rw [sFourthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    · rw [sU_add_offset]
      norm_num
      change sR x.2.1 ∉ _
      apply territory_not_mem_of_other_seed part false true (by decide)
      rw [sFourthSystem_seeds]
      simp [sFourthSeeds]

theorem sFourth_right_g_occursAt {n : ℕ}
    (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : sS x.2.1 ∉ x.1.toPolyomino.cells)
    (part : SeededPartition (sFourthSystem x frame hu hv hr)) :
    buiGPattern.OccursAt
      (quarterTurnSymmetry.transformPolyomino (part.territoryPolyomino true)).cells
      (quarterTurnSymmetry.equiv (sR x.2.1)) := by
  constructor
  · intro offset hoff
    have : offset = (0, 0) := by simpa [buiGPattern] using hoff
    subst offset
    rw [show ((0, 0) : Cell) = 0 by rfl, add_zero]
    exact transform_mem quarterTurnSymmetry (part.territoryPolyomino true)
      (part.seed_subset true (show sR x.2.1 ∈
          (sFourthSystem x frame hu hv hr).seeds true from by
        rw [sFourthSystem_seeds]
        simp [sFourthSeeds]))
  · intro offset hoff
    simp only [buiGPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h <;> subst offset
    · rw [show quarterTurnSymmetry.equiv (sR x.2.1) + (-1, 0) =
          quarterTurnSymmetry.equiv (sS x.2.1) by
          apply Prod.ext <;> dsimp [quarterTurnSymmetry, quarterTurnEquiv, sR, sS, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [sFourthSystem_cells]
      intro hm
      exact hs (Finset.mem_sdiff.mp hm).1
    · rw [show quarterTurnSymmetry.equiv (sR x.2.1) + (-1, -1) =
          quarterTurnSymmetry.equiv (sV x.2.1) by
          apply Prod.ext <;> dsimp [quarterTurnSymmetry, quarterTurnEquiv, sR, sV, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_other_seed part true false (by decide)
          (by rw [sFourthSystem_seeds]; simp [sFourthSeeds]))
    · rw [show quarterTurnSymmetry.equiv (sR x.2.1) + (0, -1) =
          quarterTurnSymmetry.equiv (sB x.2.1) by
          apply Prod.ext <;> dsimp [quarterTurnSymmetry, quarterTurnEquiv, sR, sB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [sFourthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    · rw [show quarterTurnSymmetry.equiv (sR x.2.1) + (1, -1) =
          quarterTurnSymmetry.equiv (cellAt x.2.1 1 (-1)) by
          apply Prod.ext <;> dsimp [quarterTurnSymmetry, quarterTurnEquiv, sR, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [sFourthSystem_cells]
      intro hm
      exact frame.southeast_not_mem (Finset.mem_sdiff.mp hm).1

theorem fifth_topS_not_left {n : ℕ}
    (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : sS x.2.1 ∈ x.1.toPolyomino.cells)
    (part : SeededPartition (sFifthSystem x frame hu hv hr hs)) :
    sTopS x.2.1 ∉ part.territories false := by
  by_cases ht : sTopS x.2.1 ∈ (sFifthSystem x frame hu hv hr hs).cells
  · apply territory_not_mem_of_other_seed part false true (by decide)
    rw [sFifthSystem_cells] at ht
    rw [sFifthSystem_seeds]
    simp [sFifthSeeds, chainSeed, ht]
  · exact territory_not_mem_of_not_ambient part false ht

theorem fifth_topV_not_right {n : ℕ}
    (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : sS x.2.1 ∈ x.1.toPolyomino.cells)
    (part : SeededPartition (sFifthSystem x frame hu hv hr hs)) :
    sTopV x.2.1 ∉ part.territories true := by
  by_cases ht : sTopV x.2.1 ∈ (sFifthSystem x frame hu hv hr hs).cells
  · apply territory_not_mem_of_other_seed part true false (by decide)
    rw [sFifthSystem_cells] at ht
    rw [sFifthSystem_seeds]
    simp [sFifthSeeds, chainSeed, ht]
  · exact territory_not_mem_of_not_ambient part true ht

theorem sFifth_left_y_occursAt {n : ℕ}
    (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : sS x.2.1 ∈ x.1.toPolyomino.cells)
    (part : SeededPartition (sFifthSystem x frame hu hv hr hs)) :
    buiYPattern.OccursAt
      (verticalSymmetry.transformPolyomino (part.territoryPolyomino false)).cells
      (verticalSymmetry.equiv (sV x.2.1)) := by
  constructor
  · intro offset hoff
    simp only [buiYPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with rfl | rfl
    · rw [show ((0, 0) : Cell) = 0 by rfl, add_zero]
      exact transform_mem verticalSymmetry (part.territoryPolyomino false)
        (part.seed_subset false
          (sFifthSystem_sV_mem x frame hu hv hr hs))
    · rw [show verticalSymmetry.equiv (sV x.2.1) + (1, 0) =
          verticalSymmetry.equiv (sU x.2.1) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, sV, sU, cellAt] <;> omega]
      exact transform_mem verticalSymmetry (part.territoryPolyomino false)
        (part.seed_subset false
          (sFifthSystem_sU_mem x frame hu hv hr hs))
  · intro offset hoff
    simp only [buiYPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h | h | h | h <;> subst offset
    · rw [show verticalSymmetry.equiv (sV x.2.1) + (-1, 1) =
          verticalSymmetry.equiv (sTopS x.2.1) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, sV, sTopS, cellAt] <;> omega]
      exact transform_not_mem _ _ (fifth_topS_not_left x frame hu hv hr hs part)
    · rw [show verticalSymmetry.equiv (sV x.2.1) + (-1, 0) =
          verticalSymmetry.equiv (sS x.2.1) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, sV, sS, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_other_seed part false true (by decide)
          (sFifthSystem_sS_mem x frame hu hv hr hs))
    · rw [show verticalSymmetry.equiv (sV x.2.1) + (2, 0) =
          verticalSymmetry.equiv (cellAt x.2.1 (-1) 1) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, sV, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [sFifthSystem_cells]
      intro hm
      exact frame.leftNorth_not_mem (Finset.mem_sdiff.mp hm).1
    · rw [show verticalSymmetry.equiv (sV x.2.1) + (-1, -1) =
          verticalSymmetry.equiv (sR x.2.1) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, sV, sR, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_other_seed part false true (by decide)
          (sFifthSystem_sR_mem x frame hu hv hr hs))
    · rw [show verticalSymmetry.equiv (sV x.2.1) + (0, -1) =
          verticalSymmetry.equiv (sB x.2.1) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, sV, sB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [sFifthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    · rw [show verticalSymmetry.equiv (sV x.2.1) + (1, -1) =
          verticalSymmetry.equiv (sA x.2.1) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, sV, sA, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [sFifthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    · rw [show verticalSymmetry.equiv (sV x.2.1) + (2, -1) =
          verticalSymmetry.equiv (cellAt x.2.1 (-1) 0) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, sV, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [sFifthSystem_cells]
      intro hm
      exact frame.left_not_mem (Finset.mem_sdiff.mp hm).1

theorem sFifth_right_u_occursAt {n : ℕ}
    (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : sS x.2.1 ∈ x.1.toPolyomino.cells)
    (part : SeededPartition (sFifthSystem x frame hu hv hr hs)) :
    buiUPattern.OccursAt
      (diagonalSymmetry.transformPolyomino (part.territoryPolyomino true)).cells
      (diagonalSymmetry.equiv (sR x.2.1)) := by
  constructor
  · intro offset hoff
    simp only [buiUPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with rfl | rfl
    · rw [show ((0, 0) : Cell) = 0 by rfl, add_zero]
      exact transform_mem diagonalSymmetry (part.territoryPolyomino true)
        (part.seed_subset true
          (sFifthSystem_sR_mem x frame hu hv hr hs))
    · rw [show diagonalSymmetry.equiv (sR x.2.1) + (1, 0) =
          diagonalSymmetry.equiv (sS x.2.1) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, sR, sS, cellAt] <;> omega]
      exact transform_mem diagonalSymmetry (part.territoryPolyomino true)
        (part.seed_subset true
          (sFifthSystem_sS_mem x frame hu hv hr hs))
  · intro offset hoff
    simp only [buiUPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h <;> subst offset
    · rw [show diagonalSymmetry.equiv (sR x.2.1) + (-1, -1) =
          diagonalSymmetry.equiv (cellAt x.2.1 1 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, sR, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [sFifthSystem_cells]
      intro hm
      exact frame.southeast_not_mem (Finset.mem_sdiff.mp hm).1
    · rw [show diagonalSymmetry.equiv (sR x.2.1) + (0, -1) =
          diagonalSymmetry.equiv (sB x.2.1) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, sR, sB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [sFifthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    · rw [show diagonalSymmetry.equiv (sR x.2.1) + (1, -1) =
          diagonalSymmetry.equiv (sV x.2.1) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, sR, sV, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_other_seed part true false (by decide)
          (sFifthSystem_sV_mem x frame hu hv hr hs))
    · rw [show diagonalSymmetry.equiv (sR x.2.1) + (2, -1) =
          diagonalSymmetry.equiv (sTopV x.2.1) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, sR, sTopV, cellAt] <;> omega]
      exact transform_not_mem _ _ (fifth_topV_not_right x frame hu hv hr hs part)

/-! ## The five branch encoders -/

noncomputable def sFirstMap {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∉ x.1.toPolyomino.cells) :
    MarkedOccurrence .g (n - 1) := by
  let R := sFirstRemainder x frame hu
  have hcard : R.cells.card = n - 1 := by
    change (x.1.toPolyomino.cells.erase (sA x.2.1)).card = n - 1
    exact erase_one_card x.1 (by simpa [sA] using frame.a_mem)
  exact makeMarkedPieceOfCard .g diagonalSymmetry R (sB x.2.1)
    (by exact Finset.mem_erase.mpr ⟨(sA_ne_sB _).symm,
      by simpa [sB] using frame.b_mem⟩)
    (by simpa [R, BuiNeighborhood.pattern] using sFirst_g_occursAt x frame hu) hcard

noncomputable def sSecondMap {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∉ x.1.toPolyomino.cells) :
    MarkedPair .e .e (n - 1) := by
  let D := sSecondSystem x frame hu
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hsum : L.cells.card + R.cells.card = n - 1 := by
    calc
      L.cells.card + R.cells.card = D.cells.card := bool_partition_card part
      _ = n - 1 := by
        change (x.1.toPolyomino.cells \ {sA x.2.1}).card = n - 1
        rw [Finset.sdiff_singleton_eq_erase]
        exact erase_one_card x.1 (by simpa [sA] using frame.a_mem)
  refine ⟨⟨(L.cells.card, R.cells.card), ?_⟩, ?_, ?_⟩
  · exact Finset.HasAntidiagonal.mem_antidiagonal.mpr hsum
  · exact makeMarkedPiece .e identitySymmetry L (sU x.2.1)
      (part.seed_subset false
        (by rw [sSecondSystem_seeds]; simp [sSecondSeeds]))
      (by simpa [L, BuiNeighborhood.pattern] using
        sSecond_left_e_occursAt x frame hu hv part)
  · exact makeMarkedPiece .e diagonalSymmetry R (sB x.2.1)
      (part.seed_subset true
        (by rw [sSecondSystem_seeds]; simp [sSecondSeeds]))
      (by simpa [R, BuiNeighborhood.pattern] using
        sSecond_right_e_occursAt x frame hu hv part)

noncomputable def sThirdMap {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∉ x.1.toPolyomino.cells) :
    MarkedOccurrence .t (n - 2) := by
  let R := sThirdRemainder x frame hu hv hr
  have hcard : R.cells.card = n - 2 := by
    change ((x.1.toPolyomino.cells.erase (sA x.2.1)).erase
      (sB x.2.1)).card = n - 2
    exact erase_two_card x.1 (by simpa [sA] using frame.a_mem)
      (by simpa [sB] using frame.b_mem) (sA_ne_sB _)
  exact makeMarkedPieceOfCard .t identitySymmetry R (sU x.2.1)
    (by simpa [R] using sThird_u_mem x frame hu hv hr)
    (by simpa [R, BuiNeighborhood.pattern] using
      sThird_t_occursAt x frame hu hv hr) hcard

noncomputable def sFourthMap {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : sS x.2.1 ∉ x.1.toPolyomino.cells) :
    MarkedPair .x .g (n - 2) := by
  let D := sFourthSystem x frame hu hv hr
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hsum : L.cells.card + R.cells.card = n - 2 := by
    calc
      L.cells.card + R.cells.card = D.cells.card := bool_partition_card part
      _ = n - 2 := by
        change (x.1.toPolyomino.cells \ {sA x.2.1, sB x.2.1}).card = n - 2
        rw [sdiff_pair_eq_erase_erase]
        exact erase_two_card x.1
          (by simpa [sA] using frame.a_mem)
          (by simpa [sB] using frame.b_mem) (sA_ne_sB _)
  refine ⟨⟨(L.cells.card, R.cells.card), ?_⟩, ?_, ?_⟩
  · exact Finset.HasAntidiagonal.mem_antidiagonal.mpr hsum
  · exact makeMarkedPiece .x identitySymmetry L (sU x.2.1)
      (part.seed_subset false
        (by rw [sFourthSystem_seeds]; simp [sFourthSeeds]))
      (by simpa [L, BuiNeighborhood.pattern] using
        sFourth_left_x_occursAt x frame hu hv hr hs part)
  · exact makeMarkedPiece .g quarterTurnSymmetry R (sR x.2.1)
      (part.seed_subset true
        (by rw [sFourthSystem_seeds]; simp [sFourthSeeds]))
      (by simpa [R, BuiNeighborhood.pattern] using
        sFourth_right_g_occursAt x frame hu hv hr hs part)

noncomputable def sFifthMap {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : sS x.2.1 ∈ x.1.toPolyomino.cells) :
    MarkedPair .y .u (n - 2) := by
  let D := sFifthSystem x frame hu hv hr hs
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hsum : L.cells.card + R.cells.card = n - 2 := by
    calc
      L.cells.card + R.cells.card = D.cells.card := bool_partition_card part
      _ = n - 2 := by
        change (x.1.toPolyomino.cells \ {sA x.2.1, sB x.2.1}).card = n - 2
        rw [sdiff_pair_eq_erase_erase]
        exact erase_two_card x.1
          (by simpa [sA] using frame.a_mem)
          (by simpa [sB] using frame.b_mem) (sA_ne_sB _)
  refine ⟨⟨(L.cells.card, R.cells.card), ?_⟩, ?_, ?_⟩
  · exact Finset.HasAntidiagonal.mem_antidiagonal.mpr hsum
  · exact makeMarkedPiece .y verticalSymmetry L (sV x.2.1)
      (part.seed_subset false (sFifthSystem_sV_mem x frame hu hv hr hs))
      (by simpa [L, BuiNeighborhood.pattern] using
        sFifth_left_y_occursAt x frame hu hv hr hs part)
  · exact makeMarkedPiece .u diagonalSymmetry R (sR x.2.1)
      (part.seed_subset true (sFifthSystem_sR_mem x frame hu hv hr hs))
      (by simpa [R, BuiNeighborhood.pattern] using
        sFifth_right_u_occursAt x frame hu hv hr hs part)

end GeometricFourFiveInternal

end LeanProofs.KlarnerConstant
