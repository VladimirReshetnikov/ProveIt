import KlarnerConstant.GeometricVGeometryCore

/-!
# Branch geometry and encoders for the four-branch `V` recurrence

This module proves the target patterns exposed by the occupancy branches and
constructs their finite marked-piece encoders. Reconstruction and the public
coefficient endpoint are isolated in `GeometricV`.
-/

namespace LeanProofs.KlarnerConstant
namespace GeometricVInternal

/-! ## Exposed patterns on branch remainders -/

def vFirstRemainder {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∉ x.1.toPolyomino.cells) : Polyomino :=
  eraseLeafPolyomino x.1.toPolyomino (vA x.2.1) (vB x.2.1)
    (by simpa [vA] using frame.a_mem)
    (by simpa [vB] using frame.b_mem)
    (vA_ne_vB x.2.1)
    (by
      intro c hc hadj
      rcases v_a_neighbors frame hc hadj with h | h
      · exact h
      · exact (hu (h ▸ hc)).elim)

@[simp]
theorem vFirstRemainder_cells {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∉ x.1.toPolyomino.cells) :
    (vFirstRemainder x frame hu).cells =
      x.1.toPolyomino.cells.erase (vA x.2.1) := by
  rfl

theorem vFirst_s_occursAt {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∉ x.1.toPolyomino.cells) :
    buiSPattern.OccursAt (vFirstRemainder x frame hu).cells (vB x.2.1) := by
  let a := x.2.1
  let R := vFirstRemainder x frame hu
  constructor
  · intro offset hoff
    simp only [buiSPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with rfl | rfl
    · rw [vB_add_offset]
      norm_num
      exact ⟨(vA_ne_vB x.2.1).symm,
        by simpa [vB] using frame.b_mem⟩
    · rw [vB_add_offset]
      norm_num
      exact ⟨by
          intro h
          have hx := congrArg Prod.fst h
          simp [vA, vR, cellAt] at hx <;> omega,
        by simpa [vR] using frame.r_mem⟩
  · intro offset hoff
    simp only [buiSPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h | h <;> subst offset
    · rw [vB_add_offset]
      norm_num
      intro _
      simpa [vU] using hu
    · rw [vB_add_offset]
      norm_num
      exact fun hne => (hne rfl).elim
    · rw [vB_add_offset]
      norm_num
      exact fun _ => frame.south_not_mem
    · rw [vB_add_offset]
      norm_num
      exact fun _ => frame.southeast_not_mem
    · rw [vB_add_offset]
      norm_num
      exact fun _ => frame.farSoutheast_not_mem

theorem vSecond_left_g_occursAt {n : ℕ}
    (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∉ x.1.toPolyomino.cells)
    (part : SeededPartition (vSecondSystem x frame hu hv)) :
    buiGPattern.OccursAt
      (verticalSymmetry.transformPolyomino (part.territoryPolyomino false)).cells
      (verticalSymmetry.equiv (vU x.2.1)) := by
  let a := x.2.1
  let T := part.territoryPolyomino false
  constructor
  · intro offset hoff
    have : offset = (0, 0) := by simpa [buiGPattern] using hoff
    subst offset
    rw [show verticalSymmetry.equiv (vU x.2.1) + (0, 0) =
        verticalSymmetry.equiv (vU x.2.1) by simp]
    apply transform_mem
    exact part.seed_subset false (by
      rw [vSecondSystem_seeds]
      simp [vSecondSeeds])
  · intro offset hoff
    simp only [buiGPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h <;> subst offset
    · rw [show verticalSymmetry.equiv (vU a) + (-1, 0) =
          verticalSymmetry.equiv (vV a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, vU, vV, cellAt] <;> omega]
      apply transform_not_mem
      exact territory_not_mem_of_not_ambient part false (by
        intro hm
        rw [vSecondSystem_cells] at hm
        exact hv (by simpa [a] using (Finset.mem_sdiff.mp hm).1))
    · rw [show verticalSymmetry.equiv (vU a) + (-1, -1) =
          verticalSymmetry.equiv (vB a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, vU, vB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [vSecondSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp [a])
    · rw [show verticalSymmetry.equiv (vU a) + (0, -1) =
          verticalSymmetry.equiv (vA a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, vU, vA, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [vSecondSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp [a])
    · rw [show verticalSymmetry.equiv (vU a) + (1, -1) =
          verticalSymmetry.equiv (cellAt a (-1) 0) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, vU, cellAt] <;> omega]
      apply transform_not_mem
      exact territory_not_mem_of_not_ambient part false (by
        intro hm
        rw [vSecondSystem_cells] at hm
        exact frame.left_not_mem
          (by simpa [a] using (Finset.mem_sdiff.mp hm).1))

theorem vSecond_right_g_occursAt {n : ℕ}
    (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∉ x.1.toPolyomino.cells)
    (part : SeededPartition (vSecondSystem x frame hu hv)) :
    buiGPattern.OccursAt
      (diagonalSymmetry.transformPolyomino (part.territoryPolyomino true)).cells
      (diagonalSymmetry.equiv (vR x.2.1)) := by
  let a := x.2.1
  let T := part.territoryPolyomino true
  constructor
  · intro offset hoff
    have : offset = (0, 0) := by simpa [buiGPattern] using hoff
    subst offset
    rw [show diagonalSymmetry.equiv (vR x.2.1) + (0, 0) =
        diagonalSymmetry.equiv (vR x.2.1) by simp]
    apply transform_mem
    exact part.seed_subset true (by
      rw [vSecondSystem_seeds]
      simp [vSecondSeeds])
  · intro offset hoff
    simp only [buiGPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h <;> subst offset
    · rw [show diagonalSymmetry.equiv (vR a) + (-1, 0) =
          diagonalSymmetry.equiv (cellAt a 2 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, vR, cellAt] <;> omega]
      apply transform_not_mem
      exact territory_not_mem_of_not_ambient part true (by
        intro hm
        rw [vSecondSystem_cells] at hm
        exact frame.farSoutheast_not_mem
          (by simpa [a] using (Finset.mem_sdiff.mp hm).1))
    · rw [show diagonalSymmetry.equiv (vR a) + (-1, -1) =
          diagonalSymmetry.equiv (cellAt a 1 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, vR, cellAt] <;> omega]
      apply transform_not_mem
      exact territory_not_mem_of_not_ambient part true (by
        intro hm
        rw [vSecondSystem_cells] at hm
        exact frame.southeast_not_mem
          (by simpa [a] using (Finset.mem_sdiff.mp hm).1))
    · rw [show diagonalSymmetry.equiv (vR a) + (0, -1) =
          diagonalSymmetry.equiv (vB a) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, vR, vB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [vSecondSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp [a])
    · rw [show diagonalSymmetry.equiv (vR a) + (1, -1) =
          diagonalSymmetry.equiv (vV a) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, vR, vV, cellAt] <;> omega]
      apply transform_not_mem
      exact territory_not_mem_of_not_ambient part true (by
        intro hm
        rw [vSecondSystem_cells] at hm
        exact hv (by simpa [a] using (Finset.mem_sdiff.mp hm).1))

def qThirdRemainder {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∉ x.1.toPolyomino.cells) : Polyomino :=
  eraseLowerDominoPolyomino x.1.toPolyomino
    (vA x.2.1) (vB x.2.1) (vU x.2.1) (vV x.2.1)
    (by simpa [vA] using frame.a_mem) (by simpa [vB] using frame.b_mem)
    hu hv (vA_ne_vB _) (vA_ne_vU _) (vU_ne_vB _)
    ((vA_ne_vV _).symm) (vB_ne_vV _)
    (by simpa [vU, vV] using cellAt_east x.2.1 0 1)
    (v_a_neighbors frame) (v_b_neighbors_of_r_absent frame hr)

@[simp]
theorem qThirdRemainder_cells {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∉ x.1.toPolyomino.cells) :
    (qThirdRemainder x frame hu hv hr).cells =
      (x.1.toPolyomino.cells.erase (vA x.2.1)).erase (vB x.2.1) := by
  rfl

theorem vThird_u_mem {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∉ x.1.toPolyomino.cells) :
    vU x.2.1 ∈ (qThirdRemainder x frame hu hv hr).cells := by
  exact Finset.mem_erase.mpr ⟨vU_ne_vB x.2.1,
    Finset.mem_erase.mpr ⟨(vA_ne_vU x.2.1).symm, hu⟩⟩

theorem vThird_u_occursAt {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∉ x.1.toPolyomino.cells) :
    buiUPattern.OccursAt (qThirdRemainder x frame hu hv hr).cells (vU x.2.1) := by
  constructor
  · intro offset hoffset
    simp only [buiUPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with rfl | rfl
    · rw [vU_add_offset]
      norm_num
      exact ⟨vU_ne_vB x.2.1, (vA_ne_vU x.2.1).symm, hu⟩
    · rw [vU_add_offset]
      norm_num
      exact ⟨(vB_ne_vV x.2.1).symm, (vA_ne_vV x.2.1).symm, hv⟩
  · intro offset hoffset
    simp only [buiUPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with h | h | h | h <;> subst offset
    · rw [vU_add_offset]
      norm_num
      exact fun _ _ => frame.left_not_mem
    · rw [vU_add_offset]
      norm_num
      exact fun _ hne => (hne rfl).elim
    · rw [vU_add_offset]
      norm_num
      exact fun hne => (hne rfl).elim
    · rw [vU_add_offset]
      norm_num
      exact fun _ _ => hr

theorem vFourth_left_t_occursAt {n : ℕ}
    (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : vS x.2.1 ∉ x.1.toPolyomino.cells)
    (part : SeededPartition (vFourthSystem x frame hu hv hr)) :
    buiTPattern.OccursAt
      (verticalSymmetry.transformPolyomino (part.territoryPolyomino false)).cells
      (verticalSymmetry.equiv (vV x.2.1)) := by
  let a := x.2.1
  constructor
  · intro offset hoffset
    simp only [buiTPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with rfl | rfl
    · rw [show verticalSymmetry.equiv (vV x.2.1) + (0, 0) =
          verticalSymmetry.equiv (vV x.2.1) by simp]
      exact transform_mem _ _
        (part.seed_subset false (by
          rw [vFourthSystem_seeds]
          simp [vFourthSeeds]))
    · rw [show verticalSymmetry.equiv (vV a) + (1, 0) =
          verticalSymmetry.equiv (vU a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, vV, vU, cellAt] <;> omega]
      apply transform_mem
      change vU a ∈ part.territories false
      simpa only [a] using (part.seed_subset false (by
          rw [vFourthSystem_seeds]
          simp [vFourthSeeds]))
  · intro offset hoffset
    simp only [buiTPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with h | h | h | h | h <;> subst offset
    · rw [show verticalSymmetry.equiv (vV a) + (-1, 0) =
          verticalSymmetry.equiv (vS a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, vV, vS, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_not_ambient part false (by
          intro hm
          rw [vFourthSystem_cells] at hm
          exact hs (by simpa [a] using (Finset.mem_sdiff.mp hm).1)))
    · rw [show verticalSymmetry.equiv (vV a) + (-1, -1) =
          verticalSymmetry.equiv (vR a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, vV, vR, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_other_seed part false true (by decide)
          (by rw [vFourthSystem_seeds]; simp [vFourthSeeds, a]))
    · rw [show verticalSymmetry.equiv (vV a) + (0, -1) =
          verticalSymmetry.equiv (vB a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, vV, vB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [vFourthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp [a])
    · rw [show verticalSymmetry.equiv (vV a) + (1, -1) =
          verticalSymmetry.equiv (vA a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, vV, vA, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [vFourthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp [a])
    · rw [show verticalSymmetry.equiv (vV a) + (2, -1) =
          verticalSymmetry.equiv (cellAt a (-1) 0) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, vV, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_not_ambient part false (by
          intro hm
          rw [vFourthSystem_cells] at hm
          exact frame.left_not_mem
            (by simpa [a] using (Finset.mem_sdiff.mp hm).1)))

theorem vFourth_right_e_occursAt {n : ℕ}
    (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : vS x.2.1 ∉ x.1.toPolyomino.cells)
    (part : SeededPartition (vFourthSystem x frame hu hv hr)) :
    buiEPattern.OccursAt
      (diagonalSymmetry.transformPolyomino (part.territoryPolyomino true)).cells
      (diagonalSymmetry.equiv (vR x.2.1)) := by
  let a := x.2.1
  let T := part.territoryPolyomino true
  constructor
  · intro offset hoff
    have : offset = (0, 0) := by simpa [buiEPattern] using hoff
    subst offset
    rw [show diagonalSymmetry.equiv (vR x.2.1) + (0, 0) =
        diagonalSymmetry.equiv (vR x.2.1) by simp]
    apply transform_mem
    exact part.seed_subset true (by
      rw [vFourthSystem_seeds]
      simp [vFourthSeeds])
  · intro offset hoff
    simp only [buiEPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h | h <;> subst offset
    · rw [show diagonalSymmetry.equiv (vR a) + (-1, 0) =
          diagonalSymmetry.equiv (cellAt a 2 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, vR, cellAt] <;> omega]
      exact transform_not_mem _ _ (territory_not_mem_of_not_ambient part true
        (by
          intro hm
          rw [vFourthSystem_cells] at hm
          exact frame.farSoutheast_not_mem
            (by simpa [a] using (Finset.mem_sdiff.mp hm).1)))
    · rw [show diagonalSymmetry.equiv (vR a) + (1, 0) =
          diagonalSymmetry.equiv (vS a) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, vR, vS, cellAt] <;> omega]
      exact transform_not_mem _ _ (territory_not_mem_of_not_ambient part true
        (by
          intro hm
          rw [vFourthSystem_cells] at hm
          exact hs (by simpa [a] using (Finset.mem_sdiff.mp hm).1)))
    · rw [show diagonalSymmetry.equiv (vR a) + (-1, -1) =
          diagonalSymmetry.equiv (cellAt a 1 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, vR, cellAt] <;> omega]
      exact transform_not_mem _ _ (territory_not_mem_of_not_ambient part true
        (by
          intro hm
          rw [vFourthSystem_cells] at hm
          exact frame.southeast_not_mem
            (by simpa [a] using (Finset.mem_sdiff.mp hm).1)))
    · rw [show diagonalSymmetry.equiv (vR a) + (0, -1) =
          diagonalSymmetry.equiv (vB a) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, vR, vB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [vFourthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp [a])
    · rw [show diagonalSymmetry.equiv (vR a) + (1, -1) =
          diagonalSymmetry.equiv (vV a) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, vR, vV, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_other_seed part true false (by decide)
          (by rw [vFourthSystem_seeds]; simp [vFourthSeeds, a]))

theorem fifth_topS_not_left {n : ℕ}
    (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : vS x.2.1 ∈ x.1.toPolyomino.cells)
    (part : SeededPartition (vFifthSystem x frame hu hv hr hs)) :
    vTopS x.2.1 ∉ part.territories false := by
  by_cases ht : vTopS x.2.1 ∈ (vFifthSystem x frame hu hv hr hs).cells
  · apply territory_not_mem_of_other_seed part false true (by decide)
    have ht' := ht
    rw [vFifthSystem_cells] at ht'
    rw [vFifthSystem_seeds]
    exact mem_chainSeed_iff.mpr (Or.inr (Or.inr ⟨rfl, ht'⟩))
  · exact territory_not_mem_of_not_ambient part false ht

theorem fifth_topV_not_right {n : ℕ}
    (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : vS x.2.1 ∈ x.1.toPolyomino.cells)
    (part : SeededPartition (vFifthSystem x frame hu hv hr hs)) :
    vTopV x.2.1 ∉ part.territories true := by
  by_cases ht : vTopV x.2.1 ∈ (vFifthSystem x frame hu hv hr hs).cells
  · apply territory_not_mem_of_other_seed part true false (by decide)
    have ht' := ht
    rw [vFifthSystem_cells] at ht'
    rw [vFifthSystem_seeds]
    exact mem_chainSeed_iff.mpr (Or.inr (Or.inr ⟨rfl, ht'⟩))
  · exact territory_not_mem_of_not_ambient part true ht

theorem vFifth_left_r_occursAt {n : ℕ}
    (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : vS x.2.1 ∈ x.1.toPolyomino.cells)
    (part : SeededPartition (vFifthSystem x frame hu hv hr hs)) :
    buiRPattern.OccursAt
      (verticalSymmetry.transformPolyomino (part.territoryPolyomino false)).cells
      (verticalSymmetry.equiv (vV x.2.1)) := by
  let a := x.2.1
  let T := part.territoryPolyomino false
  constructor
  · intro offset hoff
    simp only [buiRPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with rfl | rfl
    · rw [show verticalSymmetry.equiv (vV x.2.1) + (0, 0) =
          verticalSymmetry.equiv (vV x.2.1) by simp]
      exact transform_mem _ _
        (part.seed_subset false
          (vFifthSystem_vV_mem x frame hu hv hr hs))
    · rw [show verticalSymmetry.equiv (vV a) + (1, 0) =
          verticalSymmetry.equiv (vU a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, vV, vU, cellAt] <;> omega]
      apply transform_mem
      change vU a ∈ part.territories false
      simpa only [a] using
        (part.seed_subset false
          (vFifthSystem_vU_mem x frame hu hv hr hs))
  · intro offset hoff
    simp only [buiRPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h | h | h <;> subst offset
    · rw [show verticalSymmetry.equiv (vV a) + (-1, 1) =
          verticalSymmetry.equiv (vTopS a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, vV, vTopS, cellAt] <;> omega]
      exact transform_not_mem _ _ (fifth_topS_not_left x frame hu hv hr hs part)
    · rw [show verticalSymmetry.equiv (vV a) + (-1, 0) =
          verticalSymmetry.equiv (vS a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, vV, vS, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_other_seed part false true (by decide)
          (by simpa [a] using vFifthSystem_vS_mem x frame hu hv hr hs))
    · rw [show verticalSymmetry.equiv (vV a) + (-1, -1) =
          verticalSymmetry.equiv (vR a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, vV, vR, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_other_seed part false true (by decide)
          (by simpa [a] using vFifthSystem_vR_mem x frame hu hv hr hs))
    · rw [show verticalSymmetry.equiv (vV a) + (0, -1) =
          verticalSymmetry.equiv (vB a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, vV, vB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [vFifthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp [a])
    · rw [show verticalSymmetry.equiv (vV a) + (1, -1) =
          verticalSymmetry.equiv (vA a) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, vV, vA, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [vFifthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp [a])
    · rw [show verticalSymmetry.equiv (vV a) + (2, -1) =
          verticalSymmetry.equiv (cellAt a (-1) 0) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, vV, cellAt] <;> omega]
      exact transform_not_mem _ _ (territory_not_mem_of_not_ambient part false
        (by
          intro hm
          rw [vFifthSystem_cells] at hm
          exact frame.left_not_mem
            (by simpa [a] using (Finset.mem_sdiff.mp hm).1)))

theorem vFifth_right_t_occursAt {n : ℕ}
    (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : vS x.2.1 ∈ x.1.toPolyomino.cells)
    (part : SeededPartition (vFifthSystem x frame hu hv hr hs)) :
    buiTPattern.OccursAt
      (diagonalSymmetry.transformPolyomino (part.territoryPolyomino true)).cells
      (diagonalSymmetry.equiv (vR x.2.1)) := by
  let a := x.2.1
  let T := part.territoryPolyomino true
  constructor
  · intro offset hoff
    simp only [buiTPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with rfl | rfl
    · rw [show diagonalSymmetry.equiv (vR x.2.1) + (0, 0) =
          diagonalSymmetry.equiv (vR x.2.1) by simp]
      exact transform_mem _ _
        (part.seed_subset true
          (vFifthSystem_vR_mem x frame hu hv hr hs))
    · rw [show diagonalSymmetry.equiv (vR a) + (1, 0) =
          diagonalSymmetry.equiv (vS a) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, vR, vS, cellAt] <;> omega]
      apply transform_mem
      change vS a ∈ part.territories true
      simpa only [a] using
        (part.seed_subset true
          (vFifthSystem_vS_mem x frame hu hv hr hs))
  · intro offset hoff
    simp only [buiTPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h | h <;> subst offset
    · rw [show diagonalSymmetry.equiv (vR a) + (-1, 0) =
          diagonalSymmetry.equiv (cellAt a 2 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, vR, cellAt] <;> omega]
      exact transform_not_mem _ _ (territory_not_mem_of_not_ambient part true
        (by
          intro hm
          rw [vFifthSystem_cells] at hm
          exact frame.farSoutheast_not_mem
            (by simpa [a] using (Finset.mem_sdiff.mp hm).1)))
    · rw [show diagonalSymmetry.equiv (vR a) + (-1, -1) =
          diagonalSymmetry.equiv (cellAt a 1 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, vR, cellAt] <;> omega]
      exact transform_not_mem _ _ (territory_not_mem_of_not_ambient part true
        (by
          intro hm
          rw [vFifthSystem_cells] at hm
          exact frame.southeast_not_mem
            (by simpa [a] using (Finset.mem_sdiff.mp hm).1)))
    · rw [show diagonalSymmetry.equiv (vR a) + (0, -1) =
          diagonalSymmetry.equiv (vB a) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, vR, vB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [vFifthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp [a])
    · rw [show diagonalSymmetry.equiv (vR a) + (1, -1) =
          diagonalSymmetry.equiv (vV a) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, vR, vV, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_other_seed part true false (by decide)
          (by simpa [a] using vFifthSystem_vV_mem x frame hu hv hr hs))
    · rw [show diagonalSymmetry.equiv (vR a) + (2, -1) =
          diagonalSymmetry.equiv (vTopV a) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, vR, vTopV, cellAt] <;> omega]
      exact transform_not_mem _ _ (fifth_topV_not_right x frame hu hv hr hs part)

/-! ## The branch encoders -/

noncomputable def vFirstMap {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∉ x.1.toPolyomino.cells) :
    MarkedOccurrence .s (n - 1) := by
  let R := vFirstRemainder x frame hu
  have hcard : R.cells.card = n - 1 := by
    change (x.1.toPolyomino.cells.erase (vA x.2.1)).card = n - 1
    exact erase_one_card x.1 (by simpa [vA] using frame.a_mem)
  exact makeMarkedPieceOfCard .s identitySymmetry R (vB x.2.1)
    (by exact Finset.mem_erase.mpr ⟨(vA_ne_vB _).symm,
      by simpa [vB] using frame.b_mem⟩)
    (by simpa [R, BuiNeighborhood.pattern] using
      vFirst_s_occursAt x frame hu) hcard

noncomputable def vSecondMap {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∉ x.1.toPolyomino.cells) :
    MarkedPair .g .g (n - 2) := by
  let D := vSecondSystem x frame hu hv
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hsum : L.cells.card + R.cells.card = n - 2 := by
    calc
      L.cells.card + R.cells.card = D.cells.card := bool_partition_card part
      _ = n - 2 := by
        change (x.1.toPolyomino.cells \ {vA x.2.1, vB x.2.1}).card = n - 2
        rw [sdiff_pair_eq_erase_erase]
        exact erase_two_card x.1
          (by simpa [vA] using frame.a_mem)
          (by simpa [vB] using frame.b_mem) (vA_ne_vB _)
  refine ⟨⟨(L.cells.card, R.cells.card), ?_⟩, ?_, ?_⟩
  · exact Finset.HasAntidiagonal.mem_antidiagonal.mpr hsum
  · exact makeMarkedPiece .g verticalSymmetry L (vU x.2.1)
      (part.seed_subset false
        (by rw [vSecondSystem_seeds]; simp [vSecondSeeds]))
      (by simpa [L, BuiNeighborhood.pattern] using
        vSecond_left_g_occursAt x frame hu hv part)
  · exact makeMarkedPiece .g diagonalSymmetry R (vR x.2.1)
      (part.seed_subset true
        (by rw [vSecondSystem_seeds]; simp [vSecondSeeds]))
      (by simpa [R, BuiNeighborhood.pattern] using
        vSecond_right_g_occursAt x frame hu hv part)

noncomputable def vThirdMap {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∉ x.1.toPolyomino.cells) :
    MarkedOccurrence .u (n - 2) := by
  let R := qThirdRemainder x frame hu hv hr
  have hcard : R.cells.card = n - 2 := by
    change ((x.1.toPolyomino.cells.erase (vA x.2.1)).erase
      (vB x.2.1)).card = n - 2
    exact erase_two_card x.1 (by simpa [vA] using frame.a_mem)
      (by simpa [vB] using frame.b_mem) (vA_ne_vB _)
  exact makeMarkedPieceOfCard .u identitySymmetry R (vU x.2.1)
    (by simpa [R] using vThird_u_mem x frame hu hv hr)
    (by simpa [R, BuiNeighborhood.pattern] using
      vThird_u_occursAt x frame hu hv hr) hcard

noncomputable def vFourthMap {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : vS x.2.1 ∉ x.1.toPolyomino.cells) :
    MarkedPair .t .e (n - 2) := by
  let D := vFourthSystem x frame hu hv hr
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hsum : L.cells.card + R.cells.card = n - 2 := by
    calc
      L.cells.card + R.cells.card = D.cells.card := bool_partition_card part
      _ = n - 2 := by
        change (x.1.toPolyomino.cells \ {vA x.2.1, vB x.2.1}).card = n - 2
        rw [sdiff_pair_eq_erase_erase]
        exact erase_two_card x.1
          (by simpa [vA] using frame.a_mem)
          (by simpa [vB] using frame.b_mem) (vA_ne_vB _)
  refine ⟨⟨(L.cells.card, R.cells.card), ?_⟩, ?_, ?_⟩
  · exact Finset.HasAntidiagonal.mem_antidiagonal.mpr hsum
  · exact makeMarkedPiece .t verticalSymmetry L (vV x.2.1)
      (part.seed_subset false
        (by rw [vFourthSystem_seeds]; simp [vFourthSeeds]))
      (by simpa [L, BuiNeighborhood.pattern] using
        vFourth_left_t_occursAt x frame hu hv hr hs part)
  · exact makeMarkedPiece .e diagonalSymmetry R (vR x.2.1)
      (part.seed_subset true
        (by rw [vFourthSystem_seeds]; simp [vFourthSeeds]))
      (by simpa [R, BuiNeighborhood.pattern] using
        vFourth_right_e_occursAt x frame hu hv hr hs part)

noncomputable def vFifthMap {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : vS x.2.1 ∈ x.1.toPolyomino.cells) :
    MarkedPair .r .t (n - 2) := by
  let D := vFifthSystem x frame hu hv hr hs
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hsum : L.cells.card + R.cells.card = n - 2 := by
    calc
      L.cells.card + R.cells.card = D.cells.card := bool_partition_card part
      _ = n - 2 := by
        change (x.1.toPolyomino.cells \ {vA x.2.1, vB x.2.1}).card = n - 2
        rw [sdiff_pair_eq_erase_erase]
        exact erase_two_card x.1
          (by simpa [vA] using frame.a_mem)
          (by simpa [vB] using frame.b_mem) (vA_ne_vB _)
  refine ⟨⟨(L.cells.card, R.cells.card), ?_⟩, ?_, ?_⟩
  · exact Finset.HasAntidiagonal.mem_antidiagonal.mpr hsum
  · exact makeMarkedPiece .r verticalSymmetry L (vV x.2.1)
      (part.seed_subset false
        (vFifthSystem_vV_mem x frame hu hv hr hs))
      (by simpa [L, BuiNeighborhood.pattern] using
        vFifth_left_r_occursAt x frame hu hv hr hs part)
  · exact makeMarkedPiece .t diagonalSymmetry R (vR x.2.1)
      (part.seed_subset true
        (vFifthSystem_vR_mem x frame hu hv hr hs))
      (by simpa [R, BuiNeighborhood.pattern] using
        vFifth_right_t_occursAt x frame hu hv hr hs part)


end GeometricVInternal
end LeanProofs.KlarnerConstant
