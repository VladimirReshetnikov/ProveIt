import KlarnerConstant.GeometricWGeometry

/-!
# Four-branch geometric recurrence for W

This endpoint reconstructs every branch of the injective W map and exports the
natural-number, rational-coefficient, and geometric-profile inequalities.
-/

namespace LeanProofs.KlarnerConstant
namespace GeometricWInternal

/-! ## Reconstruction and injectivity -/

def recoverMarkedPair {left right : BuiNeighborhood} {m : ℕ}
    (leftSym rightSym : GridSymmetry)
    (leftOffset rightOffset : Cell) (out : MarkedPair left right m) :
    Finset Cell :=
  recoverPiece leftSym leftOffset out.2.1 ∪
    recoverPiece rightSym rightOffset out.2.2

theorem insert_image_erase (cells : Finset Cell) {a : Cell}
    (ha : a ∈ cells) (v : Cell) :
    insert (v + a) ((cells.erase a).image fun c => v + c) =
      cells.image fun c => v + c := by
  ext c
  constructor
  · intro hc
    rcases Finset.mem_insert.mp hc with hc | hc
    · subst c
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    · rcases Finset.mem_image.mp hc with ⟨d, hd, rfl⟩
      exact Finset.mem_image.mpr ⟨d, (Finset.mem_erase.mp hd).2, rfl⟩
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨d, hd, rfl⟩
    by_cases hda : d = a
    · subst d
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem <|
        Finset.mem_image.mpr ⟨d, Finset.mem_erase.mpr ⟨hda, hd⟩, rfl⟩

theorem insert_two_image_erase (cells : Finset Cell) {a b : Cell}
    (ha : a ∈ cells) (hb : b ∈ cells) (hab : a ≠ b) (v : Cell) :
    insert (v + a) (insert (v + b)
      (((cells.erase a).erase b).image fun c => v + c)) =
      cells.image fun c => v + c := by
  rw [insert_image_erase (cells.erase a)
    (Finset.mem_erase.mpr ⟨hab.symm, hb⟩) v]
  exact insert_image_erase cells ha v

theorem wFirst_reconstruct {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∉ x.1.toPolyomino.cells) :
    insert (0, 0) (recoverPiece identitySymmetry (1, 0)
      (wFirstMap x frame hu)) = anchoredCells x := by
  classical
  let R := wFirstRemainder x frame hu
  have hcard : R.cells.card = n - 1 := by
    change (x.1.toPolyomino.cells.erase (wA x.2.1)).card = n - 1
    exact erase_one_card x.1 (by simpa [wA] using frame.a_mem)
  have hrecover := recover_makeMarkedPieceOfCard .s identitySymmetry
    R x.2.1 (wB x.2.1) (1, 0)
    (by apply Prod.ext <;> dsimp [wB, cellAt] <;> omega)
    (by exact Finset.mem_erase.mpr ⟨(wA_ne_wB _).symm,
      by simpa [wB] using frame.b_mem⟩)
    (by simpa [R, BuiNeighborhood.pattern] using
      wFirst_s_occursAt x frame hu)
    hcard
  have hmap : recoverPiece identitySymmetry (1, 0) (wFirstMap x frame hu) =
      (x.1.toPolyomino.cells.erase (wA x.2.1)).image
        (fun c => -x.2.1 + c) := by
    simpa only [wFirstMap, R, wFirstRemainder_cells] using hrecover
  rw [hmap]
  change insert (0, 0)
      ((x.1.toPolyomino.cells.erase (wA x.2.1)).image
        (fun c => -x.2.1 + c)) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + wA x.2.1 by
    apply Prod.ext <;> dsimp [wA, cellAt] <;> omega]
  exact insert_image_erase _ (by simpa [wA] using frame.a_mem) _

theorem wFirstMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .w n)
      (fx : WFrame x.1.toPolyomino.cells x.2.1)
      (fy : WFrame y.1.toPolyomino.cells y.2.1)
      (hx : wU x.2.1 ∉ x.1.toPolyomino.cells)
      (hy : wU y.2.1 ∉ y.1.toPolyomino.cells),
      wFirstMap x fx hx = wFirstMap y fy hy → x = y := by
  intro x y fx fy hx hy hmap
  apply anchoredCells_injective .w n
  have h := congrArg
    (fun out : MarkedOccurrence .s (n - 1) =>
      insert (0, 0) (recoverPiece identitySymmetry (1, 0) out)) hmap
  simpa [wFirst_reconstruct] using h

theorem recoverSecondMap {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∉ x.1.toPolyomino.cells) :
    insert (0, 0) (insert (1, 0)
      (recoverMarkedPair identitySymmetry diagonalSymmetry
        (0, 1) (2, 0) (wSecondMap x frame hu hv))) = anchoredCells x := by
  classical
  let D := wSecondSystem x frame hu hv
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hL := recover_makeMarkedPiece .e identitySymmetry L x.2.1
    (wU x.2.1) (0, 1) (by apply Prod.ext <;> dsimp [wU, cellAt] <;> omega)
    (part.seed_subset false
      (by rw [wSecondSystem_seeds]; simp [wSecondSeeds]))
    (by simpa [L, BuiNeighborhood.pattern] using
      wSecond_left_e_occursAt x frame hu hv part)
  have hR := recover_makeMarkedPiece .g diagonalSymmetry R x.2.1
    (wR x.2.1) (2, 0) (by apply Prod.ext <;> dsimp [wR, cellAt] <;> omega)
    (part.seed_subset true
      (by rw [wSecondSystem_seeds]; simp [wSecondSeeds]))
    (by simpa [R, BuiNeighborhood.pattern] using
      wSecond_right_g_occursAt x frame hu hv part)
  have hcoverD : L.cells ∪ R.cells = D.cells := by
    change part.territories false ∪ part.territories true = D.cells
    rw [← part.cover]
    ext c
    simp [coveredCells, or_comm]
  have hrecover : recoverMarkedPair identitySymmetry diagonalSymmetry
      (0, 1) (2, 0) (wSecondMap x frame hu hv) =
      ((x.1.toPolyomino.cells.erase (wA x.2.1)).erase (wB x.2.1)).image
        (fun c => -x.2.1 + c) := by
    rw [show recoverMarkedPair identitySymmetry diagonalSymmetry
        (0, 1) (2, 0) (wSecondMap x frame hu hv) =
      recoverPiece identitySymmetry (0, 1)
          (makeMarkedPiece .e identitySymmetry L (wU x.2.1)
            (part.seed_subset false
              (by rw [wSecondSystem_seeds]; simp [wSecondSeeds]))
            (by simpa [L, BuiNeighborhood.pattern] using
              wSecond_left_e_occursAt x frame hu hv part)) ∪
      recoverPiece diagonalSymmetry (2, 0)
          (makeMarkedPiece .g diagonalSymmetry R (wR x.2.1)
            (part.seed_subset true
              (by rw [wSecondSystem_seeds]; simp [wSecondSeeds]))
            (by simpa [R, BuiNeighborhood.pattern] using
              wSecond_right_g_occursAt x frame hu hv part)) by
        rfl]
    rw [hL, hR, ← Finset.image_union]
    congr 1
    calc
      L.cells ∪ R.cells = D.cells := hcoverD
      _ = (x.1.toPolyomino.cells.erase (wA x.2.1)).erase
          (wB x.2.1) := by
        simp only [D, wSecondSystem_cells, sdiff_pair_eq_erase_erase]
  rw [hrecover]
  change insert (0, 0) (insert (1, 0)
      (((x.1.toPolyomino.cells.erase (wA x.2.1)).erase (wB x.2.1)).image
        (fun c => -x.2.1 + c))) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + wA x.2.1 by
      apply Prod.ext <;> dsimp [wA, cellAt] <;> omega,
    show (1, 0) = -x.2.1 + wB x.2.1 by
      apply Prod.ext <;> dsimp [wB, cellAt] <;> omega]
  exact insert_two_image_erase _ (by simpa [wA] using frame.a_mem)
    (by simpa [wB] using frame.b_mem) (wA_ne_wB _) _

theorem wSecondMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .w n)
      (fx : WFrame x.1.toPolyomino.cells x.2.1)
      (fy : WFrame y.1.toPolyomino.cells y.2.1)
      (hux : wU x.2.1 ∈ x.1.toPolyomino.cells)
      (huy : wU y.2.1 ∈ y.1.toPolyomino.cells)
      (hvx : wV x.2.1 ∉ x.1.toPolyomino.cells)
      (hvy : wV y.2.1 ∉ y.1.toPolyomino.cells),
      wSecondMap x fx hux hvx = wSecondMap y fy huy hvy → x = y := by
  intro x y fx fy hux huy hvx hvy hmap
  apply anchoredCells_injective .w n
  have h := congrArg
    (fun out : MarkedPair .e .g (n - 2) =>
      insert (0, 0) (insert (1, 0)
        (recoverMarkedPair identitySymmetry diagonalSymmetry
          (0, 1) (2, 0) out))) hmap
  simpa [recoverSecondMap] using h

theorem recoverThirdMap {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∉ x.1.toPolyomino.cells) :
    insert (0, 0) (insert (1, 0)
      (recoverPiece identitySymmetry (0, 1) (wThirdMap x frame hu hv hr))) =
      anchoredCells x := by
  classical
  let R := qThirdRemainder x frame hu hv hr
  have hcard : R.cells.card = n - 2 := by
    change ((x.1.toPolyomino.cells.erase (wA x.2.1)).erase
      (wB x.2.1)).card = n - 2
    exact erase_two_card x.1 (by simpa [wA] using frame.a_mem)
      (by simpa [wB] using frame.b_mem) (wA_ne_wB _)
  have hrecover := recover_makeMarkedPieceOfCard .u identitySymmetry R x.2.1
    (wU x.2.1) (0, 1)
    (by apply Prod.ext <;> dsimp [wU, cellAt] <;> omega)
    (by simpa [R] using wThird_u_mem x frame hu hv hr)
    (by simpa [R, BuiNeighborhood.pattern] using
      wThird_u_occursAt x frame hu hv hr)
    hcard
  have hmap : recoverPiece identitySymmetry (0, 1)
      (wThirdMap x frame hu hv hr) =
      ((x.1.toPolyomino.cells.erase (wA x.2.1)).erase (wB x.2.1)).image
        (fun c => -x.2.1 + c) := by
    simpa only [wThirdMap, R, qThirdRemainder_cells] using hrecover
  rw [hmap]
  change insert (0, 0) (insert (1, 0)
      (((x.1.toPolyomino.cells.erase (wA x.2.1)).erase (wB x.2.1)).image
        (fun c => -x.2.1 + c))) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + wA x.2.1 by
      apply Prod.ext <;> dsimp [wA, cellAt] <;> omega,
    show (1, 0) = -x.2.1 + wB x.2.1 by
      apply Prod.ext <;> dsimp [wB, cellAt] <;> omega]
  exact insert_two_image_erase _ (by simpa [wA] using frame.a_mem)
    (by simpa [wB] using frame.b_mem) (wA_ne_wB _) _

theorem wThirdMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .w n)
      (fx : WFrame x.1.toPolyomino.cells x.2.1)
      (fy : WFrame y.1.toPolyomino.cells y.2.1)
      (hux : wU x.2.1 ∈ x.1.toPolyomino.cells)
      (huy : wU y.2.1 ∈ y.1.toPolyomino.cells)
      (hvx : wV x.2.1 ∈ x.1.toPolyomino.cells)
      (hvy : wV y.2.1 ∈ y.1.toPolyomino.cells)
      (hrx : wR x.2.1 ∉ x.1.toPolyomino.cells)
      (hry : wR y.2.1 ∉ y.1.toPolyomino.cells),
      wThirdMap x fx hux hvx hrx = wThirdMap y fy huy hvy hry → x = y := by
  intro x y fx fy hux huy hvx hvy hrx hry hmap
  apply anchoredCells_injective .w n
  have h := congrArg
    (fun out : MarkedOccurrence .u (n - 2) =>
      insert (0, 0) (insert (1, 0)
        (recoverPiece identitySymmetry (0, 1) out))) hmap
  simpa [recoverThirdMap] using h

theorem recoverFourthMap {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : wS x.2.1 ∉ x.1.toPolyomino.cells) :
    insert (0, 0) (insert (1, 0)
      (recoverMarkedPair identitySymmetry diagonalSymmetry
        (0, 1) (2, 0) (wFourthMap x frame hu hv hr hs))) = anchoredCells x := by
  classical
  let D := wFourthSystem x frame hu hv hr
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hL := recover_makeMarkedPiece .x identitySymmetry L x.2.1
    (wU x.2.1) (0, 1) (by apply Prod.ext <;> dsimp [wU, cellAt] <;> omega)
    (part.seed_subset false
      (by rw [wFourthSystem_seeds]; simp [wFourthSeeds]))
    (by simpa [L, BuiNeighborhood.pattern] using
      wFourth_left_x_occursAt x frame hu hv hr hs part)
  have hR := recover_makeMarkedPiece .e diagonalSymmetry R x.2.1
    (wR x.2.1) (2, 0) (by apply Prod.ext <;> dsimp [wR, cellAt] <;> omega)
    (part.seed_subset true
      (by rw [wFourthSystem_seeds]; simp [wFourthSeeds]))
    (by simpa [R, BuiNeighborhood.pattern] using
      wFourth_right_e_occursAt x frame hu hv hr hs part)
  have hcoverD : L.cells ∪ R.cells = D.cells := by
    change part.territories false ∪ part.territories true = D.cells
    rw [← part.cover]
    ext c
    simp [coveredCells, or_comm]
  have hrecover : recoverMarkedPair identitySymmetry diagonalSymmetry
      (0, 1) (2, 0) (wFourthMap x frame hu hv hr hs) =
      ((x.1.toPolyomino.cells.erase (wA x.2.1)).erase (wB x.2.1)).image
        (fun c => -x.2.1 + c) := by
    rw [show recoverMarkedPair identitySymmetry diagonalSymmetry
        (0, 1) (2, 0) (wFourthMap x frame hu hv hr hs) =
      recoverPiece identitySymmetry (0, 1)
          (makeMarkedPiece .x identitySymmetry L (wU x.2.1)
            (part.seed_subset false
              (by rw [wFourthSystem_seeds]; simp [wFourthSeeds]))
            (by simpa [L, BuiNeighborhood.pattern] using
              wFourth_left_x_occursAt x frame hu hv hr hs part)) ∪
      recoverPiece diagonalSymmetry (2, 0)
          (makeMarkedPiece .e diagonalSymmetry R (wR x.2.1)
            (part.seed_subset true
              (by rw [wFourthSystem_seeds]; simp [wFourthSeeds]))
            (by simpa [R, BuiNeighborhood.pattern] using
              wFourth_right_e_occursAt x frame hu hv hr hs part)) by rfl]
    rw [hL, hR, ← Finset.image_union]
    congr 1
    calc
      L.cells ∪ R.cells = D.cells := hcoverD
      _ = (x.1.toPolyomino.cells.erase (wA x.2.1)).erase
          (wB x.2.1) := by
        simp only [D, wFourthSystem_cells, sdiff_pair_eq_erase_erase]
  rw [hrecover]
  change insert (0, 0) (insert (1, 0)
      (((x.1.toPolyomino.cells.erase (wA x.2.1)).erase (wB x.2.1)).image
        (fun c => -x.2.1 + c))) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + wA x.2.1 by
      apply Prod.ext <;> dsimp [wA, cellAt] <;> omega,
    show (1, 0) = -x.2.1 + wB x.2.1 by
      apply Prod.ext <;> dsimp [wB, cellAt] <;> omega]
  exact insert_two_image_erase _ (by simpa [wA] using frame.a_mem)
    (by simpa [wB] using frame.b_mem) (wA_ne_wB _) _

theorem wFourthMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .w n)
      (fx : WFrame x.1.toPolyomino.cells x.2.1)
      (fy : WFrame y.1.toPolyomino.cells y.2.1)
      (hux : wU x.2.1 ∈ x.1.toPolyomino.cells)
      (huy : wU y.2.1 ∈ y.1.toPolyomino.cells)
      (hvx : wV x.2.1 ∈ x.1.toPolyomino.cells)
      (hvy : wV y.2.1 ∈ y.1.toPolyomino.cells)
      (hrx : wR x.2.1 ∈ x.1.toPolyomino.cells)
      (hry : wR y.2.1 ∈ y.1.toPolyomino.cells)
      (hsx : wS x.2.1 ∉ x.1.toPolyomino.cells)
      (hsy : wS y.2.1 ∉ y.1.toPolyomino.cells),
      wFourthMap x fx hux hvx hrx hsx =
        wFourthMap y fy huy hvy hry hsy → x = y := by
  intro x y fx fy hux huy hvx hvy hrx hry hsx hsy hmap
  apply anchoredCells_injective .w n
  have h := congrArg
    (fun out : MarkedPair .x .e (n - 2) =>
      insert (0, 0) (insert (1, 0)
        (recoverMarkedPair identitySymmetry diagonalSymmetry
          (0, 1) (2, 0) out))) hmap
  simpa [recoverFourthMap] using h

theorem recoverFifthMap {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : wS x.2.1 ∈ x.1.toPolyomino.cells) :
    insert (0, 0) (insert (1, 0)
      (recoverMarkedPair verticalSymmetry diagonalSymmetry
        (1, 1) (2, 0) (wFifthMap x frame hu hv hr hs))) = anchoredCells x := by
  classical
  let D := wFifthSystem x frame hu hv hr hs
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hL := recover_makeMarkedPiece .y verticalSymmetry L x.2.1
    (wV x.2.1) (1, 1) (by apply Prod.ext <;> dsimp [wV, cellAt] <;> omega)
    (part.seed_subset false (wFifthSystem_wV_mem x frame hu hv hr hs))
    (by simpa [L, BuiNeighborhood.pattern] using
      wFifth_left_y_occursAt x frame hu hv hr hs part)
  have hR := recover_makeMarkedPiece .t diagonalSymmetry R x.2.1
    (wR x.2.1) (2, 0) (by apply Prod.ext <;> dsimp [wR, cellAt] <;> omega)
    (part.seed_subset true (wFifthSystem_wR_mem x frame hu hv hr hs))
    (by simpa [R, BuiNeighborhood.pattern] using
      wFifth_right_t_occursAt x frame hu hv hr hs part)
  have hcoverD : L.cells ∪ R.cells = D.cells := by
    change part.territories false ∪ part.territories true = D.cells
    rw [← part.cover]
    ext c
    simp [coveredCells, or_comm]
  have hrecover : recoverMarkedPair verticalSymmetry diagonalSymmetry
      (1, 1) (2, 0) (wFifthMap x frame hu hv hr hs) =
      ((x.1.toPolyomino.cells.erase (wA x.2.1)).erase (wB x.2.1)).image
        (fun c => -x.2.1 + c) := by
    rw [show recoverMarkedPair verticalSymmetry diagonalSymmetry
        (1, 1) (2, 0) (wFifthMap x frame hu hv hr hs) =
      recoverPiece verticalSymmetry (1, 1)
          (makeMarkedPiece .y verticalSymmetry L (wV x.2.1)
            (part.seed_subset false (wFifthSystem_wV_mem x frame hu hv hr hs))
            (by simpa [L, BuiNeighborhood.pattern] using
              wFifth_left_y_occursAt x frame hu hv hr hs part)) ∪
      recoverPiece diagonalSymmetry (2, 0)
          (makeMarkedPiece .t diagonalSymmetry R (wR x.2.1)
            (part.seed_subset true (wFifthSystem_wR_mem x frame hu hv hr hs))
            (by simpa [R, BuiNeighborhood.pattern] using
              wFifth_right_t_occursAt x frame hu hv hr hs part)) by rfl]
    rw [hL, hR, ← Finset.image_union]
    congr 1
    calc
      L.cells ∪ R.cells = D.cells := hcoverD
      _ = (x.1.toPolyomino.cells.erase (wA x.2.1)).erase
          (wB x.2.1) := by
        simp only [D, wFifthSystem_cells, sdiff_pair_eq_erase_erase]
  rw [hrecover]
  change insert (0, 0) (insert (1, 0)
      (((x.1.toPolyomino.cells.erase (wA x.2.1)).erase (wB x.2.1)).image
        (fun c => -x.2.1 + c))) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + wA x.2.1 by
      apply Prod.ext <;> dsimp [wA, cellAt] <;> omega,
    show (1, 0) = -x.2.1 + wB x.2.1 by
      apply Prod.ext <;> dsimp [wB, cellAt] <;> omega]
  exact insert_two_image_erase _ (by simpa [wA] using frame.a_mem)
    (by simpa [wB] using frame.b_mem) (wA_ne_wB _) _

theorem wFifthMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .w n)
      (fx : WFrame x.1.toPolyomino.cells x.2.1)
      (fy : WFrame y.1.toPolyomino.cells y.2.1)
      (hux : wU x.2.1 ∈ x.1.toPolyomino.cells)
      (huy : wU y.2.1 ∈ y.1.toPolyomino.cells)
      (hvx : wV x.2.1 ∈ x.1.toPolyomino.cells)
      (hvy : wV y.2.1 ∈ y.1.toPolyomino.cells)
      (hrx : wR x.2.1 ∈ x.1.toPolyomino.cells)
      (hry : wR y.2.1 ∈ y.1.toPolyomino.cells)
      (hsx : wS x.2.1 ∈ x.1.toPolyomino.cells)
      (hsy : wS y.2.1 ∈ y.1.toPolyomino.cells),
      wFifthMap x fx hux hvx hrx hsx =
        wFifthMap y fy huy hvy hry hsy → x = y := by
  intro x y fx fy hux huy hvx hvy hrx hry hsx hsy hmap
  apply anchoredCells_injective .w n
  have h := congrArg
    (fun out : MarkedPair .y .t (n - 2) =>
      insert (0, 0) (insert (1, 0)
        (recoverMarkedPair verticalSymmetry diagonalSymmetry
          (1, 1) (2, 0) out))) hmap
  simpa [recoverFifthMap] using h

/-! ## The global four-way injection and the coefficient inequality -/

abbrev WTarget (n : ℕ) :=
  Sum (MarkedOccurrence .s (n - 1))
    (Sum (MarkedPair .e .g (n - 2))
      (Sum (MarkedPair .x .e (n - 2))
        (MarkedPair .y .t (n - 2))))

noncomputable def wMarkedMap (n : ℕ) :
    MarkedOccurrence .w n → WTarget n := fun x => by
  let frame : WFrame x.1.toPolyomino.cells x.2.1 :=
    wFrame_of_occursAt (show buiWPattern.OccursAt
      x.1.toPolyomino.cells x.2.1 from marked_occursAt x)
  by_cases hu : wU x.2.1 ∈ x.1.toPolyomino.cells
  · by_cases hv : wV x.2.1 ∈ x.1.toPolyomino.cells
    · by_cases hs : wS x.2.1 ∈ x.1.toPolyomino.cells
      · exact Sum.inr (Sum.inr (Sum.inr
          (wFifthMap x frame hu hv (by simpa [wR] using frame.r_mem) hs)))
      · exact Sum.inr (Sum.inr (Sum.inl
          (wFourthMap x frame hu hv (by simpa [wR] using frame.r_mem) hs)))
    · exact Sum.inr (Sum.inl (wSecondMap x frame hu hv))
  · exact Sum.inl (wFirstMap x frame hu)

theorem wMarkedMap_injective (n : ℕ) :
    Function.Injective (wMarkedMap n) := by
  intro x y hxy
  let fx : WFrame x.1.toPolyomino.cells x.2.1 :=
    wFrame_of_occursAt (show buiWPattern.OccursAt
      x.1.toPolyomino.cells x.2.1 from marked_occursAt x)
  let fy : WFrame y.1.toPolyomino.cells y.2.1 :=
    wFrame_of_occursAt (show buiWPattern.OccursAt
      y.1.toPolyomino.cells y.2.1 from marked_occursAt y)
  by_cases hux : wU x.2.1 ∈ x.1.toPolyomino.cells
  · by_cases huy : wU y.2.1 ∈ y.1.toPolyomino.cells
    · by_cases hvx : wV x.2.1 ∈ x.1.toPolyomino.cells
      · by_cases hvy : wV y.2.1 ∈ y.1.toPolyomino.cells
        · by_cases hsx : wS x.2.1 ∈ x.1.toPolyomino.cells
          · by_cases hsy : wS y.2.1 ∈ y.1.toPolyomino.cells
            · apply wFifthMap_injective n x y fx fy hux huy hvx hvy
                (by simpa [wR] using fx.r_mem) (by simpa [wR] using fy.r_mem)
                hsx hsy
              simpa [wMarkedMap, fx, fy, hux, huy, hvx, hvy, hsx, hsy]
                using hxy
            · simp [wMarkedMap, fx, fy, hux, huy, hvx, hvy, hsx, hsy] at hxy
          · by_cases hsy : wS y.2.1 ∈ y.1.toPolyomino.cells
            · simp [wMarkedMap, fx, fy, hux, huy, hvx, hvy, hsx, hsy] at hxy
            · apply wFourthMap_injective n x y fx fy hux huy hvx hvy
                (by simpa [wR] using fx.r_mem) (by simpa [wR] using fy.r_mem)
                hsx hsy
              simpa [wMarkedMap, fx, fy, hux, huy, hvx, hvy, hsx, hsy]
                using hxy
        · by_cases hsx : wS x.2.1 ∈ x.1.toPolyomino.cells
          <;> simp [wMarkedMap, fx, fy, hux, huy, hvx, hvy, hsx] at hxy
      · by_cases hvy : wV y.2.1 ∈ y.1.toPolyomino.cells
        · by_cases hsy : wS y.2.1 ∈ y.1.toPolyomino.cells
          <;> simp [wMarkedMap, fx, fy, hux, huy, hvx, hvy, hsy] at hxy
        · apply wSecondMap_injective n x y fx fy hux huy hvx hvy
          simpa [wMarkedMap, fx, fy, hux, huy, hvx, hvy] using hxy
    · by_cases hvx : wV x.2.1 ∈ x.1.toPolyomino.cells
      · by_cases hsx : wS x.2.1 ∈ x.1.toPolyomino.cells
        <;> simp [wMarkedMap, fx, fy, hux, huy, hvx, hsx] at hxy
      · simp [wMarkedMap, fx, fy, hux, huy, hvx] at hxy
  · by_cases huy : wU y.2.1 ∈ y.1.toPolyomino.cells
    · by_cases hvy : wV y.2.1 ∈ y.1.toPolyomino.cells
      · by_cases hsy : wS y.2.1 ∈ y.1.toPolyomino.cells
        <;> simp [wMarkedMap, fx, fy, hux, huy, hvy, hsy] at hxy
      · simp [wMarkedMap, fx, fy, hux, huy, hvy] at hxy
    · apply wFirstMap_injective n x y fx fy hux huy
      simpa [wMarkedMap, fx, fy, hux, huy] using hxy

theorem card_wTarget (n : ℕ) :
    Fintype.card (WTarget n) =
      BuiNeighborhood.s.aggregateOccurrenceCount (n - 1) +
      aggregateConvolution .e .g (n - 2) +
      aggregateConvolution .x .e (n - 2) +
      aggregateConvolution .y .t (n - 2) := by
  simp only [WTarget, Fintype.card_sum, card_markedOccurrence,
    card_markedPair]
  omega


end GeometricWInternal

namespace WProof

open GeometricWInternal

/-- The exact natural-number marked-occurrence form of Bui's `W` recurrence. -/
theorem buiW_aggregateOccurrenceCount_le (n : ℕ) :
    BuiNeighborhood.w.aggregateOccurrenceCount n ≤
      BuiNeighborhood.s.aggregateOccurrenceCount (n - 1) +
      aggregateConvolution .e .g (n - 2) +
      aggregateConvolution .x .e (n - 2) +
      aggregateConvolution .y .t (n - 2) := by
  rw [← card_markedOccurrence, ← card_wTarget]
  exact Fintype.card_le_of_injective (wMarkedMap n) (wMarkedMap_injective n)

/-- The unconditional rational coefficient inequality for the actual
geometric `W` sequence. -/
theorem buiW_coefficient_le (n : ℕ) :
    BuiNeighborhood.w.coefficient n ≤
      BuiNeighborhood.s.coefficient (n - 1) +
      cauchyTwo BuiNeighborhood.e.coefficient BuiNeighborhood.g.coefficient (n - 2) +
      cauchyTwo BuiNeighborhood.x.coefficient BuiNeighborhood.e.coefficient (n - 2) +
      cauchyTwo BuiNeighborhood.y.coefficient BuiNeighborhood.t.coefficient (n - 2) := by
  rw [cauchyTwo_coefficient_eq_aggregateConvolution,
    cauchyTwo_coefficient_eq_aggregateConvolution,
    cauchyTwo_coefficient_eq_aggregateConvolution]
  unfold BuiNeighborhood.coefficient
  change (BuiNeighborhood.w.aggregateOccurrenceCount n : ℚ) ≤
    (BuiNeighborhood.s.aggregateOccurrenceCount (n - 1) : ℚ) +
      (aggregateConvolution .e .g (n - 2) : ℚ) +
      (aggregateConvolution .x .e (n - 2) : ℚ) +
      (aggregateConvolution .y .t (n - 2) : ℚ)
  exact_mod_cast buiW_aggregateOccurrenceCount_le n

/-- The `w` field required by `GeometricBuiGaps`, now discharged from finite
polyomino geometry rather than assumed. -/
theorem geometricCoefficientProfile_w_recurrence (n : ℕ) (_hn : 2 ≤ n) :
    geometricCoefficientProfile.w n ≤
      geometricCoefficientProfile.s (n - 1) +
      cauchyTwo geometricCoefficientProfile.e geometricCoefficientProfile.g (n - 2) +
      cauchyTwo geometricCoefficientProfile.x geometricCoefficientProfile.e (n - 2) +
      cauchyTwo geometricCoefficientProfile.y geometricCoefficientProfile.t (n - 2) := by
  simpa [geometricCoefficientProfile] using buiW_coefficient_le n

end WProof
export WProof
  (buiW_aggregateOccurrenceCount_le
    buiW_coefficient_le
    geometricCoefficientProfile_w_recurrence)

end LeanProofs.KlarnerConstant
