import KlarnerConstant.GeometricWGeometryCore

/-!
# Geometric W recurrence: branch geometry

The occurrence witnesses exposed by each branch remainder of the W map.
-/

namespace LeanProofs.KlarnerConstant
namespace GeometricWInternal

def wFirstRemainder {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∉ x.1.toPolyomino.cells) : Polyomino :=
  eraseLeafPolyomino x.1.toPolyomino (wA x.2.1) (wB x.2.1)
    (by simpa [wA] using frame.a_mem)
    (by simpa [wB] using frame.b_mem)
    (wA_ne_wB x.2.1)
    (by
      intro c hc hadj
      rcases w_a_neighbors frame hc hadj with h | h
      · exact h
      · exact (hu (h ▸ hc)).elim)

@[simp]
theorem wFirstRemainder_cells {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∉ x.1.toPolyomino.cells) :
    (wFirstRemainder x frame hu).cells =
      x.1.toPolyomino.cells.erase (wA x.2.1) := by
  rfl

theorem wFirst_s_occursAt {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∉ x.1.toPolyomino.cells) :
    buiSPattern.OccursAt (wFirstRemainder x frame hu).cells (wB x.2.1) := by
  let a := x.2.1
  let R := wFirstRemainder x frame hu
  constructor
  · intro offset hoff
    simp only [buiSPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with rfl | rfl
    · rw [wB_add_offset]
      norm_num
      exact ⟨(wA_ne_wB x.2.1).symm,
        by simpa [wB] using frame.b_mem⟩
    · rw [wB_add_offset]
      norm_num
      exact ⟨by
          intro h
          have hx := congrArg Prod.fst h
          simp [wA, wR, cellAt] at hx <;> omega,
        by simpa [wR] using frame.r_mem⟩
  · intro offset hoff
    simp only [buiSPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h | h <;> subst offset
    · rw [wB_add_offset]
      norm_num
      intro _
      simpa [wU] using hu
    · rw [wB_add_offset]
      norm_num
      exact fun hne => (hne rfl).elim
    · rw [wB_add_offset]
      norm_num
      exact fun _ => frame.south_not_mem
    · rw [wB_add_offset]
      norm_num
      exact fun _ => frame.southeast_not_mem
    · rw [wB_add_offset]
      norm_num
      exact fun _ => frame.farSoutheast_not_mem

theorem wSecond_left_e_occursAt {n : ℕ}
    (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∉ x.1.toPolyomino.cells)
    (part : SeededPartition (wSecondSystem x frame hu hv)) :
    buiEPattern.OccursAt (part.territoryPolyomino false).cells (wU x.2.1) := by
  let a := x.2.1
  let T := part.territoryPolyomino false
  constructor
  · intro offset hoff
    have : offset = (0, 0) := by simpa [buiEPattern] using hoff
    subst offset
    rw [wU_add_offset]
    norm_num
    change wU x.2.1 ∈ _
    exact part.seed_subset false (by
      rw [wSecondSystem_seeds]
      simp [wSecondSeeds])
  · intro offset hoff
    simp only [buiEPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h | h <;> subst offset
    · rw [wU_add_offset]
      norm_num
      apply territory_not_mem_of_not_ambient part false
      rw [wSecondSystem_cells]
      intro hm
      exact frame.leftNorth_not_mem (Finset.mem_sdiff.mp hm).1
    · rw [wU_add_offset]
      norm_num
      change wV x.2.1 ∉ _
      apply territory_not_mem_of_not_ambient part false
      rw [wSecondSystem_cells]
      intro hm
      exact hv (Finset.mem_sdiff.mp hm).1
    · rw [wU_add_offset]
      norm_num
      apply territory_not_mem_of_not_ambient part false
      rw [wSecondSystem_cells]
      intro hm
      exact frame.left_not_mem (Finset.mem_sdiff.mp hm).1
    · rw [wU_add_offset]
      norm_num
      change wA x.2.1 ∉ _
      apply territory_not_mem_of_not_ambient part false
      rw [wSecondSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    · rw [wU_add_offset]
      norm_num
      change wB x.2.1 ∉ _
      apply territory_not_mem_of_not_ambient part false
      rw [wSecondSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)

theorem wSecond_right_g_occursAt {n : ℕ}
    (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∉ x.1.toPolyomino.cells)
    (part : SeededPartition (wSecondSystem x frame hu hv)) :
    buiGPattern.OccursAt
      (diagonalSymmetry.transformPolyomino (part.territoryPolyomino true)).cells
      (diagonalSymmetry.equiv (wR x.2.1)) := by
  let a := x.2.1
  let T := part.territoryPolyomino true
  constructor
  · intro offset hoff
    have : offset = (0, 0) := by simpa [buiGPattern] using hoff
    subst offset
    rw [show diagonalSymmetry.equiv (wR x.2.1) + (0, 0) =
        diagonalSymmetry.equiv (wR x.2.1) by simp]
    apply transform_mem
    exact part.seed_subset true (by
      rw [wSecondSystem_seeds]
      simp [wSecondSeeds])
  · intro offset hoff
    simp only [buiGPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h <;> subst offset
    · rw [show diagonalSymmetry.equiv (wR a) + (-1, 0) =
          diagonalSymmetry.equiv (cellAt a 2 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, wR, cellAt] <;> omega]
      apply transform_not_mem
      exact territory_not_mem_of_not_ambient part true (by
        intro hm
        rw [wSecondSystem_cells] at hm
        exact frame.farSoutheast_not_mem
          (by simpa [a] using (Finset.mem_sdiff.mp hm).1))
    · rw [show diagonalSymmetry.equiv (wR a) + (-1, -1) =
          diagonalSymmetry.equiv (cellAt a 1 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, wR, cellAt] <;> omega]
      apply transform_not_mem
      exact territory_not_mem_of_not_ambient part true (by
        intro hm
        rw [wSecondSystem_cells] at hm
        exact frame.southeast_not_mem
          (by simpa [a] using (Finset.mem_sdiff.mp hm).1))
    · rw [show diagonalSymmetry.equiv (wR a) + (0, -1) =
          diagonalSymmetry.equiv (wB a) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, wR, wB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [wSecondSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp [a])
    · rw [show diagonalSymmetry.equiv (wR a) + (1, -1) =
          diagonalSymmetry.equiv (wV a) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, wR, wV, cellAt] <;> omega]
      apply transform_not_mem
      exact territory_not_mem_of_not_ambient part true (by
        intro hm
        rw [wSecondSystem_cells] at hm
        exact hv (by simpa [a] using (Finset.mem_sdiff.mp hm).1))

def qThirdRemainder {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∉ x.1.toPolyomino.cells) : Polyomino :=
  eraseLowerDominoPolyomino x.1.toPolyomino
    (wA x.2.1) (wB x.2.1) (wU x.2.1) (wV x.2.1)
    (by simpa [wA] using frame.a_mem) (by simpa [wB] using frame.b_mem)
    hu hv (wA_ne_wB _) (wA_ne_wU _) (wU_ne_wB _)
    ((wA_ne_wV _).symm) (wB_ne_wV _)
    (by simpa [wU, wV] using cellAt_east x.2.1 0 1)
    (w_a_neighbors frame) (w_b_neighbors_of_r_absent frame hr)

@[simp]
theorem qThirdRemainder_cells {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∉ x.1.toPolyomino.cells) :
    (qThirdRemainder x frame hu hv hr).cells =
      (x.1.toPolyomino.cells.erase (wA x.2.1)).erase (wB x.2.1) := by
  rfl

theorem wThird_u_mem {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∉ x.1.toPolyomino.cells) :
    wU x.2.1 ∈ (qThirdRemainder x frame hu hv hr).cells := by
  exact Finset.mem_erase.mpr ⟨wU_ne_wB x.2.1,
    Finset.mem_erase.mpr ⟨(wA_ne_wU x.2.1).symm, hu⟩⟩

theorem wThird_u_occursAt {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∉ x.1.toPolyomino.cells) :
    buiUPattern.OccursAt (qThirdRemainder x frame hu hv hr).cells (wU x.2.1) := by
  constructor
  · intro offset hoffset
    simp only [buiUPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with rfl | rfl
    · rw [wU_add_offset]
      norm_num
      exact ⟨wU_ne_wB x.2.1, (wA_ne_wU x.2.1).symm, hu⟩
    · rw [wU_add_offset]
      norm_num
      exact ⟨(wB_ne_wV x.2.1).symm, (wA_ne_wV x.2.1).symm, hv⟩
  · intro offset hoffset
    simp only [buiUPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with h | h | h | h <;> subst offset
    · rw [wU_add_offset]
      norm_num
      exact fun _ _ => frame.left_not_mem
    · rw [wU_add_offset]
      norm_num
      exact fun _ hne => (hne rfl).elim
    · rw [wU_add_offset]
      norm_num
      exact fun hne => (hne rfl).elim
    · rw [wU_add_offset]
      norm_num
      exact fun _ _ => hr

theorem wFourth_left_x_occursAt {n : ℕ}
    (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : wS x.2.1 ∉ x.1.toPolyomino.cells)
    (part : SeededPartition (wFourthSystem x frame hu hv hr)) :
    buiXPattern.OccursAt (part.territoryPolyomino false).cells (wU x.2.1) := by
  let a := x.2.1
  constructor
  · intro offset hoffset
    simp only [buiXPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with rfl | rfl
    · rw [wU_add_offset]
      norm_num
      change wU x.2.1 ∈ _
      exact part.seed_subset false (by
        rw [wFourthSystem_seeds]
        simp [wFourthSeeds])
    · rw [wU_add_offset]
      norm_num
      change wV x.2.1 ∈ _
      exact part.seed_subset false (by
        rw [wFourthSystem_seeds]
        simp [wFourthSeeds])
  · intro offset hoffset
    simp only [buiXPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with h | h | h | h | h | h <;> subst offset
    · rw [wU_add_offset]
      norm_num
      apply territory_not_mem_of_not_ambient part false
      rw [wFourthSystem_cells]
      intro hm
      exact frame.leftNorth_not_mem (Finset.mem_sdiff.mp hm).1
    · rw [wU_add_offset]
      norm_num
      change wS x.2.1 ∉ _
      apply territory_not_mem_of_not_ambient part false
      rw [wFourthSystem_cells]
      intro hm
      exact hs (Finset.mem_sdiff.mp hm).1
    · rw [wU_add_offset]
      norm_num
      apply territory_not_mem_of_not_ambient part false
      rw [wFourthSystem_cells]
      intro hm
      exact frame.left_not_mem (Finset.mem_sdiff.mp hm).1
    · rw [wU_add_offset]
      norm_num
      change wA x.2.1 ∉ _
      apply territory_not_mem_of_not_ambient part false
      rw [wFourthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    · rw [wU_add_offset]
      norm_num
      change wB x.2.1 ∉ _
      apply territory_not_mem_of_not_ambient part false
      rw [wFourthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    · rw [wU_add_offset]
      norm_num
      change wR x.2.1 ∉ _
      apply territory_not_mem_of_other_seed part false true (by decide)
      rw [wFourthSystem_seeds]
      simp [wFourthSeeds]

theorem wFourth_right_e_occursAt {n : ℕ}
    (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : wS x.2.1 ∉ x.1.toPolyomino.cells)
    (part : SeededPartition (wFourthSystem x frame hu hv hr)) :
    buiEPattern.OccursAt
      (diagonalSymmetry.transformPolyomino (part.territoryPolyomino true)).cells
      (diagonalSymmetry.equiv (wR x.2.1)) := by
  let a := x.2.1
  let T := part.territoryPolyomino true
  constructor
  · intro offset hoff
    have : offset = (0, 0) := by simpa [buiEPattern] using hoff
    subst offset
    rw [show diagonalSymmetry.equiv (wR x.2.1) + (0, 0) =
        diagonalSymmetry.equiv (wR x.2.1) by simp]
    apply transform_mem
    exact part.seed_subset true (by
      rw [wFourthSystem_seeds]
      simp [wFourthSeeds])
  · intro offset hoff
    simp only [buiEPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h | h <;> subst offset
    · rw [show diagonalSymmetry.equiv (wR a) + (-1, 0) =
          diagonalSymmetry.equiv (cellAt a 2 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, wR, cellAt] <;> omega]
      exact transform_not_mem _ _ (territory_not_mem_of_not_ambient part true
        (by
          intro hm
          rw [wFourthSystem_cells] at hm
          exact frame.farSoutheast_not_mem
            (by simpa [a] using (Finset.mem_sdiff.mp hm).1)))
    · rw [show diagonalSymmetry.equiv (wR a) + (1, 0) =
          diagonalSymmetry.equiv (wS a) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, wR, wS, cellAt] <;> omega]
      exact transform_not_mem _ _ (territory_not_mem_of_not_ambient part true
        (by
          intro hm
          rw [wFourthSystem_cells] at hm
          exact hs (by simpa [a] using (Finset.mem_sdiff.mp hm).1)))
    · rw [show diagonalSymmetry.equiv (wR a) + (-1, -1) =
          diagonalSymmetry.equiv (cellAt a 1 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, wR, cellAt] <;> omega]
      exact transform_not_mem _ _ (territory_not_mem_of_not_ambient part true
        (by
          intro hm
          rw [wFourthSystem_cells] at hm
          exact frame.southeast_not_mem
            (by simpa [a] using (Finset.mem_sdiff.mp hm).1)))
    · rw [show diagonalSymmetry.equiv (wR a) + (0, -1) =
          diagonalSymmetry.equiv (wB a) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, wR, wB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [wFourthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp [a])
    · rw [show diagonalSymmetry.equiv (wR a) + (1, -1) =
          diagonalSymmetry.equiv (wV a) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, wR, wV, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_other_seed part true false (by decide)
          (by rw [wFourthSystem_seeds]; simp [wFourthSeeds, a]))

theorem fifth_topS_not_left {n : ℕ}
    (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : wS x.2.1 ∈ x.1.toPolyomino.cells)
    (part : SeededPartition (wFifthSystem x frame hu hv hr hs)) :
    wTopS x.2.1 ∉ part.territories false := by
  by_cases ht : wTopS x.2.1 ∈ (wFifthSystem x frame hu hv hr hs).cells
  · apply territory_not_mem_of_other_seed part false true (by decide)
    have ht' := ht
    rw [wFifthSystem_cells] at ht'
    rw [wFifthSystem_seeds]
    exact mem_chainSeed_iff.mpr (Or.inr (Or.inr ⟨rfl, ht'⟩))
  · exact territory_not_mem_of_not_ambient part false ht

theorem fifth_topV_not_right {n : ℕ}
    (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : wS x.2.1 ∈ x.1.toPolyomino.cells)
    (part : SeededPartition (wFifthSystem x frame hu hv hr hs)) :
    wTopV x.2.1 ∉ part.territories true := by
  by_cases ht : wTopV x.2.1 ∈ (wFifthSystem x frame hu hv hr hs).cells
  · apply territory_not_mem_of_other_seed part true false (by decide)
    have ht' := ht
    rw [wFifthSystem_cells] at ht'
    rw [wFifthSystem_seeds]
    exact mem_chainSeed_iff.mpr (Or.inr (Or.inr ⟨rfl, ht'⟩))
  · exact territory_not_mem_of_not_ambient part true ht

theorem wFifth_left_y_occursAt {n : ℕ}
    (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : wS x.2.1 ∈ x.1.toPolyomino.cells)
    (part : SeededPartition (wFifthSystem x frame hu hv hr hs)) :
    buiYPattern.OccursAt
      (verticalSymmetry.transformPolyomino (part.territoryPolyomino false)).cells
      (verticalSymmetry.equiv (wV x.2.1)) := by
  let a := x.2.1
  let T := part.territoryPolyomino false
  constructor
  · intro offset hoff
    simp only [buiYPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with rfl | rfl
    · rw [show verticalSymmetry.equiv (wV x.2.1) + (0, 0) =
          verticalSymmetry.equiv (wV x.2.1) by simp]
      exact transform_mem _ _
        (part.seed_subset false
          (wFifthSystem_wV_mem x frame hu hv hr hs))
    · rw [show verticalSymmetry.equiv (wV a) + (1, 0) =
          verticalSymmetry.equiv (wU a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, wV, wU, cellAt] <;> omega]
      apply transform_mem
      change wU a ∈ part.territories false
      simpa only [a] using
        (part.seed_subset false
          (wFifthSystem_wU_mem x frame hu hv hr hs))
  · intro offset hoff
    simp only [buiYPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h | h | h | h <;> subst offset
    · rw [show verticalSymmetry.equiv (wV a) + (-1, 1) =
          verticalSymmetry.equiv (wTopS a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, wV, wTopS, cellAt] <;> omega]
      exact transform_not_mem _ _ (fifth_topS_not_left x frame hu hv hr hs part)
    · rw [show verticalSymmetry.equiv (wV a) + (-1, 0) =
          verticalSymmetry.equiv (wS a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, wV, wS, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_other_seed part false true (by decide)
          (by simpa [a] using wFifthSystem_wS_mem x frame hu hv hr hs))
    · rw [show verticalSymmetry.equiv (wV a) + (2, 0) =
          verticalSymmetry.equiv (cellAt a (-1) 1) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, wV, cellAt] <;> omega]
      exact transform_not_mem _ _ (territory_not_mem_of_not_ambient part false
        (by
          intro hm
          rw [wFifthSystem_cells] at hm
          exact frame.leftNorth_not_mem
            (by simpa [a] using (Finset.mem_sdiff.mp hm).1)))
    · rw [show verticalSymmetry.equiv (wV a) + (-1, -1) =
          verticalSymmetry.equiv (wR a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, wV, wR, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_other_seed part false true (by decide)
          (by simpa [a] using wFifthSystem_wR_mem x frame hu hv hr hs))
    · rw [show verticalSymmetry.equiv (wV a) + (0, -1) =
          verticalSymmetry.equiv (wB a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, wV, wB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [wFifthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp [a])
    · rw [show verticalSymmetry.equiv (wV a) + (1, -1) =
          verticalSymmetry.equiv (wA a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, wV, wA, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [wFifthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp [a])
    · rw [show verticalSymmetry.equiv (wV a) + (2, -1) =
          verticalSymmetry.equiv (cellAt a (-1) 0) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, wV, cellAt] <;> omega]
      exact transform_not_mem _ _ (territory_not_mem_of_not_ambient part false
        (by
          intro hm
          rw [wFifthSystem_cells] at hm
          exact frame.left_not_mem
            (by simpa [a] using (Finset.mem_sdiff.mp hm).1)))

theorem wFifth_right_t_occursAt {n : ℕ}
    (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : wS x.2.1 ∈ x.1.toPolyomino.cells)
    (part : SeededPartition (wFifthSystem x frame hu hv hr hs)) :
    buiTPattern.OccursAt
      (diagonalSymmetry.transformPolyomino (part.territoryPolyomino true)).cells
      (diagonalSymmetry.equiv (wR x.2.1)) := by
  let a := x.2.1
  let T := part.territoryPolyomino true
  constructor
  · intro offset hoff
    simp only [buiTPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with rfl | rfl
    · rw [show diagonalSymmetry.equiv (wR x.2.1) + (0, 0) =
          diagonalSymmetry.equiv (wR x.2.1) by simp]
      exact transform_mem _ _
        (part.seed_subset true
          (wFifthSystem_wR_mem x frame hu hv hr hs))
    · rw [show diagonalSymmetry.equiv (wR a) + (1, 0) =
          diagonalSymmetry.equiv (wS a) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, wR, wS, cellAt] <;> omega]
      apply transform_mem
      change wS a ∈ part.territories true
      simpa only [a] using
        (part.seed_subset true
          (wFifthSystem_wS_mem x frame hu hv hr hs))
  · intro offset hoff
    simp only [buiTPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h | h <;> subst offset
    · rw [show diagonalSymmetry.equiv (wR a) + (-1, 0) =
          diagonalSymmetry.equiv (cellAt a 2 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, wR, cellAt] <;> omega]
      exact transform_not_mem _ _ (territory_not_mem_of_not_ambient part true
        (by
          intro hm
          rw [wFifthSystem_cells] at hm
          exact frame.farSoutheast_not_mem
            (by simpa [a] using (Finset.mem_sdiff.mp hm).1)))
    · rw [show diagonalSymmetry.equiv (wR a) + (-1, -1) =
          diagonalSymmetry.equiv (cellAt a 1 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, wR, cellAt] <;> omega]
      exact transform_not_mem _ _ (territory_not_mem_of_not_ambient part true
        (by
          intro hm
          rw [wFifthSystem_cells] at hm
          exact frame.southeast_not_mem
            (by simpa [a] using (Finset.mem_sdiff.mp hm).1)))
    · rw [show diagonalSymmetry.equiv (wR a) + (0, -1) =
          diagonalSymmetry.equiv (wB a) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, wR, wB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [wFifthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp [a])
    · rw [show diagonalSymmetry.equiv (wR a) + (1, -1) =
          diagonalSymmetry.equiv (wV a) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, wR, wV, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_other_seed part true false (by decide)
          (by simpa [a] using wFifthSystem_wV_mem x frame hu hv hr hs))
    · rw [show diagonalSymmetry.equiv (wR a) + (2, -1) =
          diagonalSymmetry.equiv (wTopV a) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, wR, wTopV, cellAt] <;> omega]
      exact transform_not_mem _ _ (fifth_topV_not_right x frame hu hv hr hs part)

/-! ## The branch encoders -/

noncomputable def wFirstMap {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∉ x.1.toPolyomino.cells) :
    MarkedOccurrence .s (n - 1) := by
  let R := wFirstRemainder x frame hu
  have hcard : R.cells.card = n - 1 := by
    change (x.1.toPolyomino.cells.erase (wA x.2.1)).card = n - 1
    exact erase_one_card x.1 (by simpa [wA] using frame.a_mem)
  exact makeMarkedPieceOfCard .s identitySymmetry R (wB x.2.1)
    (by exact Finset.mem_erase.mpr ⟨(wA_ne_wB _).symm,
      by simpa [wB] using frame.b_mem⟩)
    (by simpa [R, BuiNeighborhood.pattern] using
      wFirst_s_occursAt x frame hu) hcard

noncomputable def wSecondMap {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∉ x.1.toPolyomino.cells) :
    MarkedPair .e .g (n - 2) := by
  let D := wSecondSystem x frame hu hv
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hsum : L.cells.card + R.cells.card = n - 2 := by
    calc
      L.cells.card + R.cells.card = D.cells.card := bool_partition_card part
      _ = n - 2 := by
        change (x.1.toPolyomino.cells \ {wA x.2.1, wB x.2.1}).card = n - 2
        rw [sdiff_pair_eq_erase_erase]
        exact erase_two_card x.1
          (by simpa [wA] using frame.a_mem)
          (by simpa [wB] using frame.b_mem) (wA_ne_wB _)
  refine ⟨⟨(L.cells.card, R.cells.card), ?_⟩, ?_, ?_⟩
  · exact Finset.HasAntidiagonal.mem_antidiagonal.mpr hsum
  · exact makeMarkedPiece .e identitySymmetry L (wU x.2.1)
      (part.seed_subset false
        (by rw [wSecondSystem_seeds]; simp [wSecondSeeds]))
      (by simpa [L, BuiNeighborhood.pattern] using
        wSecond_left_e_occursAt x frame hu hv part)
  · exact makeMarkedPiece .g diagonalSymmetry R (wR x.2.1)
      (part.seed_subset true
        (by rw [wSecondSystem_seeds]; simp [wSecondSeeds]))
      (by simpa [R, BuiNeighborhood.pattern] using
        wSecond_right_g_occursAt x frame hu hv part)

noncomputable def wThirdMap {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∉ x.1.toPolyomino.cells) :
    MarkedOccurrence .u (n - 2) := by
  let R := qThirdRemainder x frame hu hv hr
  have hcard : R.cells.card = n - 2 := by
    change ((x.1.toPolyomino.cells.erase (wA x.2.1)).erase
      (wB x.2.1)).card = n - 2
    exact erase_two_card x.1 (by simpa [wA] using frame.a_mem)
      (by simpa [wB] using frame.b_mem) (wA_ne_wB _)
  exact makeMarkedPieceOfCard .u identitySymmetry R (wU x.2.1)
    (by simpa [R] using wThird_u_mem x frame hu hv hr)
    (by simpa [R, BuiNeighborhood.pattern] using
      wThird_u_occursAt x frame hu hv hr) hcard

noncomputable def wFourthMap {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : wS x.2.1 ∉ x.1.toPolyomino.cells) :
    MarkedPair .x .e (n - 2) := by
  let D := wFourthSystem x frame hu hv hr
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hsum : L.cells.card + R.cells.card = n - 2 := by
    calc
      L.cells.card + R.cells.card = D.cells.card := bool_partition_card part
      _ = n - 2 := by
        change (x.1.toPolyomino.cells \ {wA x.2.1, wB x.2.1}).card = n - 2
        rw [sdiff_pair_eq_erase_erase]
        exact erase_two_card x.1
          (by simpa [wA] using frame.a_mem)
          (by simpa [wB] using frame.b_mem) (wA_ne_wB _)
  refine ⟨⟨(L.cells.card, R.cells.card), ?_⟩, ?_, ?_⟩
  · exact Finset.HasAntidiagonal.mem_antidiagonal.mpr hsum
  · exact makeMarkedPiece .x identitySymmetry L (wU x.2.1)
      (part.seed_subset false
        (by rw [wFourthSystem_seeds]; simp [wFourthSeeds]))
      (by simpa [L, BuiNeighborhood.pattern] using
        wFourth_left_x_occursAt x frame hu hv hr hs part)
  · exact makeMarkedPiece .e diagonalSymmetry R (wR x.2.1)
      (part.seed_subset true
        (by rw [wFourthSystem_seeds]; simp [wFourthSeeds]))
      (by simpa [R, BuiNeighborhood.pattern] using
        wFourth_right_e_occursAt x frame hu hv hr hs part)

noncomputable def wFifthMap {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : wS x.2.1 ∈ x.1.toPolyomino.cells) :
    MarkedPair .y .t (n - 2) := by
  let D := wFifthSystem x frame hu hv hr hs
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hsum : L.cells.card + R.cells.card = n - 2 := by
    calc
      L.cells.card + R.cells.card = D.cells.card := bool_partition_card part
      _ = n - 2 := by
        change (x.1.toPolyomino.cells \ {wA x.2.1, wB x.2.1}).card = n - 2
        rw [sdiff_pair_eq_erase_erase]
        exact erase_two_card x.1
          (by simpa [wA] using frame.a_mem)
          (by simpa [wB] using frame.b_mem) (wA_ne_wB _)
  refine ⟨⟨(L.cells.card, R.cells.card), ?_⟩, ?_, ?_⟩
  · exact Finset.HasAntidiagonal.mem_antidiagonal.mpr hsum
  · exact makeMarkedPiece .y verticalSymmetry L (wV x.2.1)
      (part.seed_subset false
        (wFifthSystem_wV_mem x frame hu hv hr hs))
      (by simpa [L, BuiNeighborhood.pattern] using
        wFifth_left_y_occursAt x frame hu hv hr hs part)
  · exact makeMarkedPiece .t diagonalSymmetry R (wR x.2.1)
      (part.seed_subset true
        (wFifthSystem_wR_mem x frame hu hv hr hs))
      (by simpa [R, BuiNeighborhood.pattern] using
        wFifth_right_t_occursAt x frame hu hv hr hs part)

end GeometricWInternal
end LeanProofs.KlarnerConstant
