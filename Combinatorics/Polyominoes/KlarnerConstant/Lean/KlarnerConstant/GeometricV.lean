import KlarnerConstant.GeometricVGeometry

/-!
# Four-branch geometric recurrence for V

This module formalizes the `V` row of Appendix B in Bui's convolutional
polyomino argument. For every `n` it proves

```
V(n) <= S(n-1) + (G*G)(n-2) + (T*E)(n-2) + (R*T)(n-2).
```

The proof partitions globally marked occurrences by local occupancy, maps each
branch injectively to a one-factor or convolution target, and supplies explicit
lossless reconstructors after normalization.

The implementation is split along declaration dependencies as
`GeometricVCore` -> `GeometricVGeometryCore` -> `GeometricVGeometry` ->
`GeometricV`; this endpoint retains the original exported theorem surface.
-/

namespace LeanProofs.KlarnerConstant
namespace GeometricVInternal

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

theorem vFirst_reconstruct {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∉ x.1.toPolyomino.cells) :
    insert (0, 0) (recoverPiece identitySymmetry (1, 0)
      (vFirstMap x frame hu)) = anchoredCells x := by
  classical
  let R := vFirstRemainder x frame hu
  have hcard : R.cells.card = n - 1 := by
    change (x.1.toPolyomino.cells.erase (vA x.2.1)).card = n - 1
    exact erase_one_card x.1 (by simpa [vA] using frame.a_mem)
  have hrecover := recover_makeMarkedPieceOfCard .s identitySymmetry
    R x.2.1 (vB x.2.1) (1, 0)
    (by apply Prod.ext <;> dsimp [vB, cellAt] <;> omega)
    (by exact Finset.mem_erase.mpr ⟨(vA_ne_vB _).symm,
      by simpa [vB] using frame.b_mem⟩)
    (by simpa [R, BuiNeighborhood.pattern] using
      vFirst_s_occursAt x frame hu)
    hcard
  have hmap : recoverPiece identitySymmetry (1, 0) (vFirstMap x frame hu) =
      (x.1.toPolyomino.cells.erase (vA x.2.1)).image
        (fun c => -x.2.1 + c) := by
    simpa only [vFirstMap, R, vFirstRemainder_cells] using hrecover
  rw [hmap]
  change insert (0, 0)
      ((x.1.toPolyomino.cells.erase (vA x.2.1)).image
        (fun c => -x.2.1 + c)) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + vA x.2.1 by
    apply Prod.ext <;> dsimp [vA, cellAt] <;> omega]
  exact insert_image_erase _ (by simpa [vA] using frame.a_mem) _

theorem vFirstMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .v n)
      (fx : VFrame x.1.toPolyomino.cells x.2.1)
      (fy : VFrame y.1.toPolyomino.cells y.2.1)
      (hx : vU x.2.1 ∉ x.1.toPolyomino.cells)
      (hy : vU y.2.1 ∉ y.1.toPolyomino.cells),
      vFirstMap x fx hx = vFirstMap y fy hy → x = y := by
  intro x y fx fy hx hy hmap
  apply anchoredCells_injective .v n
  have h := congrArg
    (fun out : MarkedOccurrence .s (n - 1) =>
      insert (0, 0) (recoverPiece identitySymmetry (1, 0) out)) hmap
  simpa [vFirst_reconstruct] using h

theorem recoverSecondMap {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∉ x.1.toPolyomino.cells) :
    insert (0, 0) (insert (1, 0)
      (recoverMarkedPair verticalSymmetry diagonalSymmetry
        (0, 1) (2, 0) (vSecondMap x frame hu hv))) = anchoredCells x := by
  classical
  let D := vSecondSystem x frame hu hv
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hL := recover_makeMarkedPiece .g verticalSymmetry L x.2.1
    (vU x.2.1) (0, 1) (by apply Prod.ext <;> dsimp [vU, cellAt] <;> omega)
    (part.seed_subset false
      (by rw [vSecondSystem_seeds]; simp [vSecondSeeds]))
    (by simpa [L, BuiNeighborhood.pattern] using
      vSecond_left_g_occursAt x frame hu hv part)
  have hR := recover_makeMarkedPiece .g diagonalSymmetry R x.2.1
    (vR x.2.1) (2, 0) (by apply Prod.ext <;> dsimp [vR, cellAt] <;> omega)
    (part.seed_subset true
      (by rw [vSecondSystem_seeds]; simp [vSecondSeeds]))
    (by simpa [R, BuiNeighborhood.pattern] using
      vSecond_right_g_occursAt x frame hu hv part)
  have hcoverD : L.cells ∪ R.cells = D.cells := by
    change part.territories false ∪ part.territories true = D.cells
    rw [← part.cover]
    ext c
    simp [coveredCells, or_comm]
  have hrecover : recoverMarkedPair verticalSymmetry diagonalSymmetry
      (0, 1) (2, 0) (vSecondMap x frame hu hv) =
      ((x.1.toPolyomino.cells.erase (vA x.2.1)).erase (vB x.2.1)).image
        (fun c => -x.2.1 + c) := by
    rw [show recoverMarkedPair verticalSymmetry diagonalSymmetry
        (0, 1) (2, 0) (vSecondMap x frame hu hv) =
      recoverPiece verticalSymmetry (0, 1)
          (makeMarkedPiece .g verticalSymmetry L (vU x.2.1)
            (part.seed_subset false
              (by rw [vSecondSystem_seeds]; simp [vSecondSeeds]))
            (by simpa [L, BuiNeighborhood.pattern] using
              vSecond_left_g_occursAt x frame hu hv part)) ∪
      recoverPiece diagonalSymmetry (2, 0)
          (makeMarkedPiece .g diagonalSymmetry R (vR x.2.1)
            (part.seed_subset true
              (by rw [vSecondSystem_seeds]; simp [vSecondSeeds]))
            (by simpa [R, BuiNeighborhood.pattern] using
              vSecond_right_g_occursAt x frame hu hv part)) by
        rfl]
    rw [hL, hR, ← Finset.image_union]
    congr 1
    calc
      L.cells ∪ R.cells = D.cells := hcoverD
      _ = (x.1.toPolyomino.cells.erase (vA x.2.1)).erase
          (vB x.2.1) := by
        simp only [D, vSecondSystem_cells, sdiff_pair_eq_erase_erase]
  rw [hrecover]
  change insert (0, 0) (insert (1, 0)
      (((x.1.toPolyomino.cells.erase (vA x.2.1)).erase (vB x.2.1)).image
        (fun c => -x.2.1 + c))) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + vA x.2.1 by
      apply Prod.ext <;> dsimp [vA, cellAt] <;> omega,
    show (1, 0) = -x.2.1 + vB x.2.1 by
      apply Prod.ext <;> dsimp [vB, cellAt] <;> omega]
  exact insert_two_image_erase _ (by simpa [vA] using frame.a_mem)
    (by simpa [vB] using frame.b_mem) (vA_ne_vB _) _

theorem vSecondMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .v n)
      (fx : VFrame x.1.toPolyomino.cells x.2.1)
      (fy : VFrame y.1.toPolyomino.cells y.2.1)
      (hux : vU x.2.1 ∈ x.1.toPolyomino.cells)
      (huy : vU y.2.1 ∈ y.1.toPolyomino.cells)
      (hvx : vV x.2.1 ∉ x.1.toPolyomino.cells)
      (hvy : vV y.2.1 ∉ y.1.toPolyomino.cells),
      vSecondMap x fx hux hvx = vSecondMap y fy huy hvy → x = y := by
  intro x y fx fy hux huy hvx hvy hmap
  apply anchoredCells_injective .v n
  have h := congrArg
    (fun out : MarkedPair .g .g (n - 2) =>
      insert (0, 0) (insert (1, 0)
        (recoverMarkedPair verticalSymmetry diagonalSymmetry
          (0, 1) (2, 0) out))) hmap
  simpa [recoverSecondMap] using h

theorem recoverThirdMap {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∉ x.1.toPolyomino.cells) :
    insert (0, 0) (insert (1, 0)
      (recoverPiece identitySymmetry (0, 1) (vThirdMap x frame hu hv hr))) =
      anchoredCells x := by
  classical
  let R := qThirdRemainder x frame hu hv hr
  have hcard : R.cells.card = n - 2 := by
    change ((x.1.toPolyomino.cells.erase (vA x.2.1)).erase
      (vB x.2.1)).card = n - 2
    exact erase_two_card x.1 (by simpa [vA] using frame.a_mem)
      (by simpa [vB] using frame.b_mem) (vA_ne_vB _)
  have hrecover := recover_makeMarkedPieceOfCard .u identitySymmetry R x.2.1
    (vU x.2.1) (0, 1) (by apply Prod.ext <;> dsimp [vU, cellAt] <;> omega)
    (by simpa [R] using vThird_u_mem x frame hu hv hr)
    (by simpa [R, BuiNeighborhood.pattern] using
      vThird_u_occursAt x frame hu hv hr)
    hcard
  have hmap : recoverPiece identitySymmetry (0, 1)
      (vThirdMap x frame hu hv hr) =
      ((x.1.toPolyomino.cells.erase (vA x.2.1)).erase (vB x.2.1)).image
        (fun c => -x.2.1 + c) := by
    simpa only [vThirdMap, R, qThirdRemainder_cells] using hrecover
  rw [hmap]
  change insert (0, 0) (insert (1, 0)
      (((x.1.toPolyomino.cells.erase (vA x.2.1)).erase (vB x.2.1)).image
        (fun c => -x.2.1 + c))) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + vA x.2.1 by
      apply Prod.ext <;> dsimp [vA, cellAt] <;> omega,
    show (1, 0) = -x.2.1 + vB x.2.1 by
      apply Prod.ext <;> dsimp [vB, cellAt] <;> omega]
  exact insert_two_image_erase _ (by simpa [vA] using frame.a_mem)
    (by simpa [vB] using frame.b_mem) (vA_ne_vB _) _

theorem vThirdMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .v n)
      (fx : VFrame x.1.toPolyomino.cells x.2.1)
      (fy : VFrame y.1.toPolyomino.cells y.2.1)
      (hux : vU x.2.1 ∈ x.1.toPolyomino.cells)
      (huy : vU y.2.1 ∈ y.1.toPolyomino.cells)
      (hvx : vV x.2.1 ∈ x.1.toPolyomino.cells)
      (hvy : vV y.2.1 ∈ y.1.toPolyomino.cells)
      (hrx : vR x.2.1 ∉ x.1.toPolyomino.cells)
      (hry : vR y.2.1 ∉ y.1.toPolyomino.cells),
      vThirdMap x fx hux hvx hrx = vThirdMap y fy huy hvy hry → x = y := by
  intro x y fx fy hux huy hvx hvy hrx hry hmap
  apply anchoredCells_injective .v n
  have h := congrArg
    (fun out : MarkedOccurrence .u (n - 2) =>
      insert (0, 0) (insert (1, 0)
        (recoverPiece identitySymmetry (0, 1) out))) hmap
  simpa [recoverThirdMap] using h

theorem recoverFourthMap {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : vS x.2.1 ∉ x.1.toPolyomino.cells) :
    insert (0, 0) (insert (1, 0)
      (recoverMarkedPair verticalSymmetry diagonalSymmetry
        (1, 1) (2, 0) (vFourthMap x frame hu hv hr hs))) = anchoredCells x := by
  classical
  let D := vFourthSystem x frame hu hv hr
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hL := recover_makeMarkedPiece .t verticalSymmetry L x.2.1
    (vV x.2.1) (1, 1) (by apply Prod.ext <;> dsimp [vV, cellAt] <;> omega)
    (part.seed_subset false
      (by rw [vFourthSystem_seeds]; simp [vFourthSeeds]))
    (by simpa [L, BuiNeighborhood.pattern] using
      vFourth_left_t_occursAt x frame hu hv hr hs part)
  have hR := recover_makeMarkedPiece .e diagonalSymmetry R x.2.1
    (vR x.2.1) (2, 0) (by apply Prod.ext <;> dsimp [vR, cellAt] <;> omega)
    (part.seed_subset true
      (by rw [vFourthSystem_seeds]; simp [vFourthSeeds]))
    (by simpa [R, BuiNeighborhood.pattern] using
      vFourth_right_e_occursAt x frame hu hv hr hs part)
  have hcoverD : L.cells ∪ R.cells = D.cells := by
    change part.territories false ∪ part.territories true = D.cells
    rw [← part.cover]
    ext c
    simp [coveredCells, or_comm]
  have hrecover : recoverMarkedPair verticalSymmetry diagonalSymmetry
      (1, 1) (2, 0) (vFourthMap x frame hu hv hr hs) =
      ((x.1.toPolyomino.cells.erase (vA x.2.1)).erase (vB x.2.1)).image
        (fun c => -x.2.1 + c) := by
    rw [show recoverMarkedPair verticalSymmetry diagonalSymmetry
        (1, 1) (2, 0) (vFourthMap x frame hu hv hr hs) =
      recoverPiece verticalSymmetry (1, 1)
          (makeMarkedPiece .t verticalSymmetry L (vV x.2.1)
            (part.seed_subset false
              (by rw [vFourthSystem_seeds]; simp [vFourthSeeds]))
            (by simpa [L, BuiNeighborhood.pattern] using
              vFourth_left_t_occursAt x frame hu hv hr hs part)) ∪
      recoverPiece diagonalSymmetry (2, 0)
          (makeMarkedPiece .e diagonalSymmetry R (vR x.2.1)
            (part.seed_subset true
              (by rw [vFourthSystem_seeds]; simp [vFourthSeeds]))
            (by simpa [R, BuiNeighborhood.pattern] using
              vFourth_right_e_occursAt x frame hu hv hr hs part)) by rfl]
    rw [hL, hR, ← Finset.image_union]
    congr 1
    calc
      L.cells ∪ R.cells = D.cells := hcoverD
      _ = (x.1.toPolyomino.cells.erase (vA x.2.1)).erase
          (vB x.2.1) := by
        simp only [D, vFourthSystem_cells, sdiff_pair_eq_erase_erase]
  rw [hrecover]
  change insert (0, 0) (insert (1, 0)
      (((x.1.toPolyomino.cells.erase (vA x.2.1)).erase (vB x.2.1)).image
        (fun c => -x.2.1 + c))) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + vA x.2.1 by
      apply Prod.ext <;> dsimp [vA, cellAt] <;> omega,
    show (1, 0) = -x.2.1 + vB x.2.1 by
      apply Prod.ext <;> dsimp [vB, cellAt] <;> omega]
  exact insert_two_image_erase _ (by simpa [vA] using frame.a_mem)
    (by simpa [vB] using frame.b_mem) (vA_ne_vB _) _

theorem vFourthMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .v n)
      (fx : VFrame x.1.toPolyomino.cells x.2.1)
      (fy : VFrame y.1.toPolyomino.cells y.2.1)
      (hux : vU x.2.1 ∈ x.1.toPolyomino.cells)
      (huy : vU y.2.1 ∈ y.1.toPolyomino.cells)
      (hvx : vV x.2.1 ∈ x.1.toPolyomino.cells)
      (hvy : vV y.2.1 ∈ y.1.toPolyomino.cells)
      (hrx : vR x.2.1 ∈ x.1.toPolyomino.cells)
      (hry : vR y.2.1 ∈ y.1.toPolyomino.cells)
      (hsx : vS x.2.1 ∉ x.1.toPolyomino.cells)
      (hsy : vS y.2.1 ∉ y.1.toPolyomino.cells),
      vFourthMap x fx hux hvx hrx hsx =
        vFourthMap y fy huy hvy hry hsy → x = y := by
  intro x y fx fy hux huy hvx hvy hrx hry hsx hsy hmap
  apply anchoredCells_injective .v n
  have h := congrArg
    (fun out : MarkedPair .t .e (n - 2) =>
      insert (0, 0) (insert (1, 0)
        (recoverMarkedPair verticalSymmetry diagonalSymmetry
          (1, 1) (2, 0) out))) hmap
  simpa [recoverFourthMap] using h

theorem recoverFifthMap {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : vS x.2.1 ∈ x.1.toPolyomino.cells) :
    insert (0, 0) (insert (1, 0)
      (recoverMarkedPair verticalSymmetry diagonalSymmetry
        (1, 1) (2, 0) (vFifthMap x frame hu hv hr hs))) = anchoredCells x := by
  classical
  let D := vFifthSystem x frame hu hv hr hs
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hL := recover_makeMarkedPiece .r verticalSymmetry L x.2.1
    (vV x.2.1) (1, 1) (by apply Prod.ext <;> dsimp [vV, cellAt] <;> omega)
    (part.seed_subset false (vFifthSystem_vV_mem x frame hu hv hr hs))
    (by simpa [L, BuiNeighborhood.pattern] using
      vFifth_left_r_occursAt x frame hu hv hr hs part)
  have hR := recover_makeMarkedPiece .t diagonalSymmetry R x.2.1
    (vR x.2.1) (2, 0) (by apply Prod.ext <;> dsimp [vR, cellAt] <;> omega)
    (part.seed_subset true (vFifthSystem_vR_mem x frame hu hv hr hs))
    (by simpa [R, BuiNeighborhood.pattern] using
      vFifth_right_t_occursAt x frame hu hv hr hs part)
  have hcoverD : L.cells ∪ R.cells = D.cells := by
    change part.territories false ∪ part.territories true = D.cells
    rw [← part.cover]
    ext c
    simp [coveredCells, or_comm]
  have hrecover : recoverMarkedPair verticalSymmetry diagonalSymmetry
      (1, 1) (2, 0) (vFifthMap x frame hu hv hr hs) =
      ((x.1.toPolyomino.cells.erase (vA x.2.1)).erase (vB x.2.1)).image
        (fun c => -x.2.1 + c) := by
    rw [show recoverMarkedPair verticalSymmetry diagonalSymmetry
        (1, 1) (2, 0) (vFifthMap x frame hu hv hr hs) =
      recoverPiece verticalSymmetry (1, 1)
          (makeMarkedPiece .r verticalSymmetry L (vV x.2.1)
            (part.seed_subset false (vFifthSystem_vV_mem x frame hu hv hr hs))
            (by simpa [L, BuiNeighborhood.pattern] using
              vFifth_left_r_occursAt x frame hu hv hr hs part)) ∪
      recoverPiece diagonalSymmetry (2, 0)
          (makeMarkedPiece .t diagonalSymmetry R (vR x.2.1)
            (part.seed_subset true (vFifthSystem_vR_mem x frame hu hv hr hs))
            (by simpa [R, BuiNeighborhood.pattern] using
              vFifth_right_t_occursAt x frame hu hv hr hs part)) by rfl]
    rw [hL, hR, ← Finset.image_union]
    congr 1
    calc
      L.cells ∪ R.cells = D.cells := hcoverD
      _ = (x.1.toPolyomino.cells.erase (vA x.2.1)).erase
          (vB x.2.1) := by
        simp only [D, vFifthSystem_cells, sdiff_pair_eq_erase_erase]
  rw [hrecover]
  change insert (0, 0) (insert (1, 0)
      (((x.1.toPolyomino.cells.erase (vA x.2.1)).erase (vB x.2.1)).image
        (fun c => -x.2.1 + c))) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + vA x.2.1 by
      apply Prod.ext <;> dsimp [vA, cellAt] <;> omega,
    show (1, 0) = -x.2.1 + vB x.2.1 by
      apply Prod.ext <;> dsimp [vB, cellAt] <;> omega]
  exact insert_two_image_erase _ (by simpa [vA] using frame.a_mem)
    (by simpa [vB] using frame.b_mem) (vA_ne_vB _) _
theorem vFifthMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .v n)
      (fx : VFrame x.1.toPolyomino.cells x.2.1)
      (fy : VFrame y.1.toPolyomino.cells y.2.1)
      (hux : vU x.2.1 ∈ x.1.toPolyomino.cells)
      (huy : vU y.2.1 ∈ y.1.toPolyomino.cells)
      (hvx : vV x.2.1 ∈ x.1.toPolyomino.cells)
      (hvy : vV y.2.1 ∈ y.1.toPolyomino.cells)
      (hrx : vR x.2.1 ∈ x.1.toPolyomino.cells)
      (hry : vR y.2.1 ∈ y.1.toPolyomino.cells)
      (hsx : vS x.2.1 ∈ x.1.toPolyomino.cells)
      (hsy : vS y.2.1 ∈ y.1.toPolyomino.cells),
      vFifthMap x fx hux hvx hrx hsx =
        vFifthMap y fy huy hvy hry hsy → x = y := by
  intro x y fx fy hux huy hvx hvy hrx hry hsx hsy hmap
  apply anchoredCells_injective .v n
  have h := congrArg
    (fun out : MarkedPair .r .t (n - 2) =>
      insert (0, 0) (insert (1, 0)
        (recoverMarkedPair verticalSymmetry diagonalSymmetry
          (1, 1) (2, 0) out))) hmap
  simpa [recoverFifthMap] using h

/-! ## The global four-way injection and the coefficient inequality -/

abbrev VTarget (n : ℕ) :=
  Sum (MarkedOccurrence .s (n - 1))
    (Sum (MarkedPair .g .g (n - 2))
      (Sum (MarkedPair .t .e (n - 2))
        (MarkedPair .r .t (n - 2))))

noncomputable def vMarkedMap (n : ℕ) :
    MarkedOccurrence .v n → VTarget n := fun x => by
  let frame : VFrame x.1.toPolyomino.cells x.2.1 :=
    vFrame_of_occursAt (show buiVPattern.OccursAt
      x.1.toPolyomino.cells x.2.1 from marked_occursAt x)
  by_cases hu : vU x.2.1 ∈ x.1.toPolyomino.cells
  · by_cases hv : vV x.2.1 ∈ x.1.toPolyomino.cells
    · by_cases hs : vS x.2.1 ∈ x.1.toPolyomino.cells
      · exact Sum.inr (Sum.inr (Sum.inr
          (vFifthMap x frame hu hv (by simpa [vR] using frame.r_mem) hs)))
      · exact Sum.inr (Sum.inr (Sum.inl
          (vFourthMap x frame hu hv (by simpa [vR] using frame.r_mem) hs)))
    · exact Sum.inr (Sum.inl (vSecondMap x frame hu hv))
  · exact Sum.inl (vFirstMap x frame hu)

theorem vMarkedMap_injective (n : ℕ) :
    Function.Injective (vMarkedMap n) := by
  intro x y hxy
  let fx : VFrame x.1.toPolyomino.cells x.2.1 :=
    vFrame_of_occursAt (show buiVPattern.OccursAt
      x.1.toPolyomino.cells x.2.1 from marked_occursAt x)
  let fy : VFrame y.1.toPolyomino.cells y.2.1 :=
    vFrame_of_occursAt (show buiVPattern.OccursAt
      y.1.toPolyomino.cells y.2.1 from marked_occursAt y)
  by_cases hux : vU x.2.1 ∈ x.1.toPolyomino.cells
  · by_cases huy : vU y.2.1 ∈ y.1.toPolyomino.cells
    · by_cases hvx : vV x.2.1 ∈ x.1.toPolyomino.cells
      · by_cases hvy : vV y.2.1 ∈ y.1.toPolyomino.cells
        · by_cases hsx : vS x.2.1 ∈ x.1.toPolyomino.cells
          · by_cases hsy : vS y.2.1 ∈ y.1.toPolyomino.cells
            · apply vFifthMap_injective n x y fx fy hux huy hvx hvy
                (by simpa [vR] using fx.r_mem) (by simpa [vR] using fy.r_mem)
                hsx hsy
              simpa [vMarkedMap, fx, fy, hux, huy, hvx, hvy, hsx, hsy]
                using hxy
            · simp [vMarkedMap, fx, fy, hux, huy, hvx, hvy, hsx, hsy] at hxy
          · by_cases hsy : vS y.2.1 ∈ y.1.toPolyomino.cells
            · simp [vMarkedMap, fx, fy, hux, huy, hvx, hvy, hsx, hsy] at hxy
            · apply vFourthMap_injective n x y fx fy hux huy hvx hvy
                (by simpa [vR] using fx.r_mem) (by simpa [vR] using fy.r_mem)
                hsx hsy
              simpa [vMarkedMap, fx, fy, hux, huy, hvx, hvy, hsx, hsy]
                using hxy
        · by_cases hsx : vS x.2.1 ∈ x.1.toPolyomino.cells
          <;> simp [vMarkedMap, fx, fy, hux, huy, hvx, hvy, hsx] at hxy
      · by_cases hvy : vV y.2.1 ∈ y.1.toPolyomino.cells
        · by_cases hsy : vS y.2.1 ∈ y.1.toPolyomino.cells
          <;> simp [vMarkedMap, fx, fy, hux, huy, hvx, hvy, hsy] at hxy
        · apply vSecondMap_injective n x y fx fy hux huy hvx hvy
          simpa [vMarkedMap, fx, fy, hux, huy, hvx, hvy] using hxy
    · by_cases hvx : vV x.2.1 ∈ x.1.toPolyomino.cells
      · by_cases hsx : vS x.2.1 ∈ x.1.toPolyomino.cells
        <;> simp [vMarkedMap, fx, fy, hux, huy, hvx, hsx] at hxy
      · simp [vMarkedMap, fx, fy, hux, huy, hvx] at hxy
  · by_cases huy : vU y.2.1 ∈ y.1.toPolyomino.cells
    · by_cases hvy : vV y.2.1 ∈ y.1.toPolyomino.cells
      · by_cases hsy : vS y.2.1 ∈ y.1.toPolyomino.cells
        <;> simp [vMarkedMap, fx, fy, hux, huy, hvy, hsy] at hxy
      · simp [vMarkedMap, fx, fy, hux, huy, hvy] at hxy
    · apply vFirstMap_injective n x y fx fy hux huy
      simpa [vMarkedMap, fx, fy, hux, huy] using hxy

theorem card_vTarget (n : ℕ) :
    Fintype.card (VTarget n) =
      BuiNeighborhood.s.aggregateOccurrenceCount (n - 1) +
      aggregateConvolution .g .g (n - 2) +
      aggregateConvolution .t .e (n - 2) +
      aggregateConvolution .r .t (n - 2) := by
  simp only [VTarget, Fintype.card_sum, card_markedOccurrence,
    card_markedPair]
  omega


end GeometricVInternal

namespace VProof

open GeometricVInternal

/-- The exact natural-number marked-occurrence form of Bui's `V` recurrence. -/
theorem buiV_aggregateOccurrenceCount_le (n : ℕ) :
    BuiNeighborhood.v.aggregateOccurrenceCount n ≤
      BuiNeighborhood.s.aggregateOccurrenceCount (n - 1) +
      aggregateConvolution .g .g (n - 2) +
      aggregateConvolution .t .e (n - 2) +
      aggregateConvolution .r .t (n - 2) := by
  rw [← card_markedOccurrence, ← card_vTarget]
  exact Fintype.card_le_of_injective (vMarkedMap n) (vMarkedMap_injective n)

/-- The unconditional rational coefficient inequality for the actual
geometric `V` sequence. -/
theorem buiV_coefficient_le (n : ℕ) :
    BuiNeighborhood.v.coefficient n ≤
      BuiNeighborhood.s.coefficient (n - 1) +
      cauchyTwo BuiNeighborhood.g.coefficient BuiNeighborhood.g.coefficient (n - 2) +
      cauchyTwo BuiNeighborhood.t.coefficient BuiNeighborhood.e.coefficient (n - 2) +
      cauchyTwo BuiNeighborhood.r.coefficient BuiNeighborhood.t.coefficient (n - 2) := by
  rw [cauchyTwo_coefficient_eq_aggregateConvolution,
    cauchyTwo_coefficient_eq_aggregateConvolution,
    cauchyTwo_coefficient_eq_aggregateConvolution]
  unfold BuiNeighborhood.coefficient
  change (BuiNeighborhood.v.aggregateOccurrenceCount n : ℚ) ≤
    (BuiNeighborhood.s.aggregateOccurrenceCount (n - 1) : ℚ) +
      (aggregateConvolution .g .g (n - 2) : ℚ) +
      (aggregateConvolution .t .e (n - 2) : ℚ) +
      (aggregateConvolution .r .t (n - 2) : ℚ)
  exact_mod_cast buiV_aggregateOccurrenceCount_le n

/-- The `v` field required by `GeometricBuiGaps`, now discharged from finite
polyomino geometry rather than assumed. -/
theorem geometricCoefficientProfile_v_recurrence (n : ℕ) (_hn : 2 ≤ n) :
    geometricCoefficientProfile.v n ≤
      geometricCoefficientProfile.s (n - 1) +
      cauchyTwo geometricCoefficientProfile.g geometricCoefficientProfile.g (n - 2) +
      cauchyTwo geometricCoefficientProfile.t geometricCoefficientProfile.e (n - 2) +
      cauchyTwo geometricCoefficientProfile.r geometricCoefficientProfile.t (n - 2) := by
  simpa [geometricCoefficientProfile] using buiV_coefficient_le n

end VProof
export VProof
  (buiV_aggregateOccurrenceCount_le
    buiV_coefficient_le
    geometricCoefficientProfile_v_recurrence)

end LeanProofs.KlarnerConstant
