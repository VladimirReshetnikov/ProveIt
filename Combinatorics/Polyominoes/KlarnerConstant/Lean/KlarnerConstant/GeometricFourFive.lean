import KlarnerConstant.GeometricFourFiveGeometry

/-!
# A five-branch geometric recurrence

This file formalizes the `S` row of Appendix B in Bui's convolutional
polyomino argument.  For `n >= 2` it proves

```
S(n) <= G(n-1) + (E*E)(n-1) + T(n-2)
       + (X*G)(n-2) + (Y*U)(n-2).
```

The proof works with globally marked occurrences.  It partitions them by the
successive occupancy of the four cells `u`, `v`, `r`, and `s` around the
marked lower domino.  In the convolution branches the one- or two-cell
deletion remainder is divided into two connected seeded territories.  The
last branch uses two additional optional seed cells.  They are precisely the
cells which must belong to the opposite territory in order to expose the
marked `Y` and `U` boundaries; this makes explicit a detail suppressed by the
small diagrams in the paper.

Three lattice symmetries are used to put the exposed boundaries in the fixed
orientations of `Patterns.lean`.  All are implemented as additive
equivalences, and the decoder below proves that normalizing the two factors
does not lose the relative placement data carried by their marked anchors.
-/

namespace LeanProofs.KlarnerConstant

namespace GeometricFourFiveInternal

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

theorem sFirst_reconstruct {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∉ x.1.toPolyomino.cells) :
    insert (0, 0) (recoverPiece diagonalSymmetry (1, 0)
      (sFirstMap x frame hu)) = anchoredCells x := by
  classical
  let R := sFirstRemainder x frame hu
  have hcard : R.cells.card = n - 1 := by
    change (x.1.toPolyomino.cells.erase (sA x.2.1)).card = n - 1
    exact erase_one_card x.1 (by simpa [sA] using frame.a_mem)
  have hrecover := recover_makeMarkedPieceOfCard .g diagonalSymmetry
    R x.2.1 (sB x.2.1) (1, 0)
    (by apply Prod.ext <;> dsimp [sB, cellAt] <;> omega)
    (by exact Finset.mem_erase.mpr ⟨(sA_ne_sB _).symm,
      by simpa [sB] using frame.b_mem⟩)
    (by simpa [R, BuiNeighborhood.pattern] using sFirst_g_occursAt x frame hu) hcard
  have hRcells : R.cells = x.1.toPolyomino.cells.erase (sA x.2.1) := rfl
  have hmap : recoverPiece diagonalSymmetry (1, 0) (sFirstMap x frame hu) =
      (x.1.toPolyomino.cells.erase (sA x.2.1)).image
        (fun c => -x.2.1 + c) := by
    calc
      _ = R.cells.image (fun c => -x.2.1 + c) := by
        simpa only [sFirstMap, R, sFirstRemainder] using hrecover
      _ = (x.1.toPolyomino.cells.erase (sA x.2.1)).image
          (fun c => -x.2.1 + c) := by rw [hRcells]
  rw [hmap]
  change insert (0, 0)
      ((x.1.toPolyomino.cells.erase (sA x.2.1)).image
        (fun c => -x.2.1 + c)) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + sA x.2.1 by
    apply Prod.ext <;> dsimp [sA, cellAt] <;> omega]
  exact insert_image_erase _ (by simpa [sA] using frame.a_mem) _

theorem sFirstMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .s n)
      (fx : SFrame x.1.toPolyomino.cells x.2.1)
      (fy : SFrame y.1.toPolyomino.cells y.2.1)
      (hx : sU x.2.1 ∉ x.1.toPolyomino.cells)
      (hy : sU y.2.1 ∉ y.1.toPolyomino.cells),
      sFirstMap x fx hx = sFirstMap y fy hy → x = y := by
  intro x y fx fy hx hy hmap
  apply anchoredCells_injective .s n
  have h := congrArg
    (fun out : MarkedOccurrence .g (n - 1) =>
      insert (0, 0) (recoverPiece diagonalSymmetry (1, 0) out)) hmap
  simpa [sFirst_reconstruct] using h

theorem recoverSecondMap {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∉ x.1.toPolyomino.cells) :
    insert (0, 0)
      (recoverMarkedPair identitySymmetry diagonalSymmetry
        (0, 1) (1, 0) (sSecondMap x frame hu hv)) = anchoredCells x := by
  classical
  let D := sSecondSystem x frame hu
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hL := recover_makeMarkedPiece .e identitySymmetry L x.2.1
    (sU x.2.1) (0, 1)
    (by apply Prod.ext <;> dsimp [sU, cellAt] <;> omega)
    (part.seed_subset false
      (by rw [sSecondSystem_seeds]; simp [sSecondSeeds]))
    (by simpa [L, BuiNeighborhood.pattern] using
      sSecond_left_e_occursAt x frame hu hv part)
  have hR := recover_makeMarkedPiece .e diagonalSymmetry R x.2.1
    (sB x.2.1) (1, 0)
    (by apply Prod.ext <;> dsimp [sB, cellAt] <;> omega)
    (part.seed_subset true
      (by rw [sSecondSystem_seeds]; simp [sSecondSeeds]))
    (by simpa [R, BuiNeighborhood.pattern] using
      sSecond_right_e_occursAt x frame hu hv part)
  have hcoverD : L.cells ∪ R.cells = D.cells := by
    change part.territories false ∪ part.territories true = D.cells
    rw [← part.cover]
    ext c
    simp [coveredCells, or_comm]
  have hrecover : recoverMarkedPair identitySymmetry diagonalSymmetry
      (0, 1) (1, 0) (sSecondMap x frame hu hv) =
      (x.1.toPolyomino.cells.erase (sA x.2.1)).image
        (fun c => -x.2.1 + c) := by
    rw [show recoverMarkedPair identitySymmetry diagonalSymmetry
        (0, 1) (1, 0) (sSecondMap x frame hu hv) =
      recoverPiece identitySymmetry (0, 1)
          (makeMarkedPiece .e identitySymmetry L (sU x.2.1)
            (part.seed_subset false
              (by rw [sSecondSystem_seeds]; simp [sSecondSeeds]))
            (by simpa [L, BuiNeighborhood.pattern] using
              sSecond_left_e_occursAt x frame hu hv part)) ∪
      recoverPiece diagonalSymmetry (1, 0)
          (makeMarkedPiece .e diagonalSymmetry R (sB x.2.1)
            (part.seed_subset true
              (by rw [sSecondSystem_seeds]; simp [sSecondSeeds]))
            (by simpa [R, BuiNeighborhood.pattern] using
              sSecond_right_e_occursAt x frame hu hv part)) by
        rfl]
    rw [hL, hR, ← Finset.image_union]
    congr 1
    calc
      L.cells ∪ R.cells = D.cells := hcoverD
      _ = x.1.toPolyomino.cells.erase (sA x.2.1) := by
        simp only [D, sSecondSystem_cells, Finset.sdiff_singleton_eq_erase]
  rw [hrecover]
  change insert (0, 0)
      ((x.1.toPolyomino.cells.erase (sA x.2.1)).image
        (fun c => -x.2.1 + c)) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + sA x.2.1 by
    apply Prod.ext <;> dsimp [sA, cellAt] <;> omega]
  exact insert_image_erase _ (by simpa [sA] using frame.a_mem) _

theorem sSecondMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .s n)
      (fx : SFrame x.1.toPolyomino.cells x.2.1)
      (fy : SFrame y.1.toPolyomino.cells y.2.1)
      (hux : sU x.2.1 ∈ x.1.toPolyomino.cells)
      (huy : sU y.2.1 ∈ y.1.toPolyomino.cells)
      (hvx : sV x.2.1 ∉ x.1.toPolyomino.cells)
      (hvy : sV y.2.1 ∉ y.1.toPolyomino.cells),
      sSecondMap x fx hux hvx = sSecondMap y fy huy hvy → x = y := by
  intro x y fx fy hux huy hvx hvy hmap
  apply anchoredCells_injective .s n
  have h := congrArg
    (fun out : MarkedPair .e .e (n - 1) =>
      insert (0, 0) (recoverMarkedPair identitySymmetry diagonalSymmetry
        (0, 1) (1, 0) out)) hmap
  simpa [recoverSecondMap] using h

theorem recoverThirdMap {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∉ x.1.toPolyomino.cells) :
    insert (0, 0) (insert (1, 0)
      (recoverPiece identitySymmetry (0, 1) (sThirdMap x frame hu hv hr))) =
      anchoredCells x := by
  classical
  let R := sThirdRemainder x frame hu hv hr
  have hcard : R.cells.card = n - 2 := by
    change ((x.1.toPolyomino.cells.erase (sA x.2.1)).erase
      (sB x.2.1)).card = n - 2
    exact erase_two_card x.1 (by simpa [sA] using frame.a_mem)
      (by simpa [sB] using frame.b_mem) (sA_ne_sB _)
  have hrecover := recover_makeMarkedPieceOfCard .t identitySymmetry R x.2.1
    (sU x.2.1) (0, 1)
    (by apply Prod.ext <;> dsimp [sU, cellAt] <;> omega)
    (by simpa [R] using sThird_u_mem x frame hu hv hr)
    (by simpa [R, BuiNeighborhood.pattern] using
      sThird_t_occursAt x frame hu hv hr) hcard
  have hRcells : R.cells =
      (x.1.toPolyomino.cells.erase (sA x.2.1)).erase (sB x.2.1) := rfl
  have hmap : recoverPiece identitySymmetry (0, 1)
      (sThirdMap x frame hu hv hr) =
      ((x.1.toPolyomino.cells.erase (sA x.2.1)).erase (sB x.2.1)).image
        (fun c => -x.2.1 + c) := by
    calc
      _ = R.cells.image (fun c => -x.2.1 + c) := by
        simpa only [sThirdMap, R, sThirdRemainder] using hrecover
      _ = ((x.1.toPolyomino.cells.erase (sA x.2.1)).erase
          (sB x.2.1)).image (fun c => -x.2.1 + c) := by rw [hRcells]
  rw [hmap]
  change insert (0, 0) (insert (1, 0)
      (((x.1.toPolyomino.cells.erase (sA x.2.1)).erase (sB x.2.1)).image
        (fun c => -x.2.1 + c))) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + sA x.2.1 by
      apply Prod.ext <;> dsimp [sA, cellAt] <;> omega,
    show (1, 0) = -x.2.1 + sB x.2.1 by
      apply Prod.ext <;> dsimp [sB, cellAt] <;> omega]
  exact insert_two_image_erase _ (by simpa [sA] using frame.a_mem)
    (by simpa [sB] using frame.b_mem) (sA_ne_sB _) _

theorem sThirdMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .s n)
      (fx : SFrame x.1.toPolyomino.cells x.2.1)
      (fy : SFrame y.1.toPolyomino.cells y.2.1)
      (hux : sU x.2.1 ∈ x.1.toPolyomino.cells)
      (huy : sU y.2.1 ∈ y.1.toPolyomino.cells)
      (hvx : sV x.2.1 ∈ x.1.toPolyomino.cells)
      (hvy : sV y.2.1 ∈ y.1.toPolyomino.cells)
      (hrx : sR x.2.1 ∉ x.1.toPolyomino.cells)
      (hry : sR y.2.1 ∉ y.1.toPolyomino.cells),
      sThirdMap x fx hux hvx hrx = sThirdMap y fy huy hvy hry → x = y := by
  intro x y fx fy hux huy hvx hvy hrx hry hmap
  apply anchoredCells_injective .s n
  have h := congrArg
    (fun out : MarkedOccurrence .t (n - 2) =>
      insert (0, 0) (insert (1, 0)
        (recoverPiece identitySymmetry (0, 1) out))) hmap
  simpa [recoverThirdMap] using h

theorem recoverFourthMap {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : sS x.2.1 ∉ x.1.toPolyomino.cells) :
    insert (0, 0) (insert (1, 0)
      (recoverMarkedPair identitySymmetry quarterTurnSymmetry
        (0, 1) (2, 0) (sFourthMap x frame hu hv hr hs))) = anchoredCells x := by
  classical
  let D := sFourthSystem x frame hu hv hr
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hL := recover_makeMarkedPiece .x identitySymmetry L x.2.1
    (sU x.2.1) (0, 1)
    (by apply Prod.ext <;> dsimp [sU, cellAt] <;> omega)
    (part.seed_subset false
      (by rw [sFourthSystem_seeds]; simp [sFourthSeeds]))
    (by simpa [L, BuiNeighborhood.pattern] using
      sFourth_left_x_occursAt x frame hu hv hr hs part)
  have hR := recover_makeMarkedPiece .g quarterTurnSymmetry R x.2.1
    (sR x.2.1) (2, 0)
    (by apply Prod.ext <;> dsimp [sR, cellAt] <;> omega)
    (part.seed_subset true
      (by rw [sFourthSystem_seeds]; simp [sFourthSeeds]))
    (by simpa [R, BuiNeighborhood.pattern] using
      sFourth_right_g_occursAt x frame hu hv hr hs part)
  have hcoverD : L.cells ∪ R.cells = D.cells := by
    change part.territories false ∪ part.territories true = D.cells
    rw [← part.cover]
    ext c
    simp [coveredCells, or_comm]
  have hrecover : recoverMarkedPair identitySymmetry quarterTurnSymmetry
      (0, 1) (2, 0) (sFourthMap x frame hu hv hr hs) =
      ((x.1.toPolyomino.cells.erase (sA x.2.1)).erase (sB x.2.1)).image
        (fun c => -x.2.1 + c) := by
    rw [show recoverMarkedPair identitySymmetry quarterTurnSymmetry
        (0, 1) (2, 0) (sFourthMap x frame hu hv hr hs) =
      recoverPiece identitySymmetry (0, 1)
          (makeMarkedPiece .x identitySymmetry L (sU x.2.1)
            (part.seed_subset false
              (by rw [sFourthSystem_seeds]; simp [sFourthSeeds]))
            (by simpa [L, BuiNeighborhood.pattern] using
              sFourth_left_x_occursAt x frame hu hv hr hs part)) ∪
      recoverPiece quarterTurnSymmetry (2, 0)
          (makeMarkedPiece .g quarterTurnSymmetry R (sR x.2.1)
            (part.seed_subset true
              (by rw [sFourthSystem_seeds]; simp [sFourthSeeds]))
            (by simpa [R, BuiNeighborhood.pattern] using
              sFourth_right_g_occursAt x frame hu hv hr hs part)) by rfl]
    rw [hL, hR, ← Finset.image_union]
    congr 1
    calc
      L.cells ∪ R.cells = D.cells := hcoverD
      _ = (x.1.toPolyomino.cells.erase (sA x.2.1)).erase
          (sB x.2.1) := by
        simp only [D, sFourthSystem_cells, sdiff_pair_eq_erase_erase]
  rw [hrecover]
  change insert (0, 0) (insert (1, 0)
      (((x.1.toPolyomino.cells.erase (sA x.2.1)).erase (sB x.2.1)).image
        (fun c => -x.2.1 + c))) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + sA x.2.1 by
      apply Prod.ext <;> dsimp [sA, cellAt] <;> omega,
    show (1, 0) = -x.2.1 + sB x.2.1 by
      apply Prod.ext <;> dsimp [sB, cellAt] <;> omega]
  exact insert_two_image_erase _ (by simpa [sA] using frame.a_mem)
    (by simpa [sB] using frame.b_mem) (sA_ne_sB _) _

theorem sFourthMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .s n)
      (fx : SFrame x.1.toPolyomino.cells x.2.1)
      (fy : SFrame y.1.toPolyomino.cells y.2.1)
      (hux : sU x.2.1 ∈ x.1.toPolyomino.cells)
      (huy : sU y.2.1 ∈ y.1.toPolyomino.cells)
      (hvx : sV x.2.1 ∈ x.1.toPolyomino.cells)
      (hvy : sV y.2.1 ∈ y.1.toPolyomino.cells)
      (hrx : sR x.2.1 ∈ x.1.toPolyomino.cells)
      (hry : sR y.2.1 ∈ y.1.toPolyomino.cells)
      (hsx : sS x.2.1 ∉ x.1.toPolyomino.cells)
      (hsy : sS y.2.1 ∉ y.1.toPolyomino.cells),
      sFourthMap x fx hux hvx hrx hsx =
        sFourthMap y fy huy hvy hry hsy → x = y := by
  intro x y fx fy hux huy hvx hvy hrx hry hsx hsy hmap
  apply anchoredCells_injective .s n
  have h := congrArg
    (fun out : MarkedPair .x .g (n - 2) =>
      insert (0, 0) (insert (1, 0)
        (recoverMarkedPair identitySymmetry quarterTurnSymmetry
          (0, 1) (2, 0) out))) hmap
  simpa [recoverFourthMap] using h

theorem recoverFifthMap {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : sS x.2.1 ∈ x.1.toPolyomino.cells) :
    insert (0, 0) (insert (1, 0)
      (recoverMarkedPair verticalSymmetry diagonalSymmetry
        (1, 1) (2, 0) (sFifthMap x frame hu hv hr hs))) = anchoredCells x := by
  classical
  let D := sFifthSystem x frame hu hv hr hs
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hL := recover_makeMarkedPiece .y verticalSymmetry L x.2.1
    (sV x.2.1) (1, 1)
    (by apply Prod.ext <;> dsimp [sV, cellAt] <;> omega)
    (part.seed_subset false (sFifthSystem_sV_mem x frame hu hv hr hs))
    (by simpa [L, BuiNeighborhood.pattern] using
      sFifth_left_y_occursAt x frame hu hv hr hs part)
  have hR := recover_makeMarkedPiece .u diagonalSymmetry R x.2.1
    (sR x.2.1) (2, 0)
    (by apply Prod.ext <;> dsimp [sR, cellAt] <;> omega)
    (part.seed_subset true (sFifthSystem_sR_mem x frame hu hv hr hs))
    (by simpa [R, BuiNeighborhood.pattern] using
      sFifth_right_u_occursAt x frame hu hv hr hs part)
  have hcoverD : L.cells ∪ R.cells = D.cells := by
    change part.territories false ∪ part.territories true = D.cells
    rw [← part.cover]
    ext c
    simp [coveredCells, or_comm]
  have hrecover : recoverMarkedPair verticalSymmetry diagonalSymmetry
      (1, 1) (2, 0) (sFifthMap x frame hu hv hr hs) =
      ((x.1.toPolyomino.cells.erase (sA x.2.1)).erase (sB x.2.1)).image
        (fun c => -x.2.1 + c) := by
    rw [show recoverMarkedPair verticalSymmetry diagonalSymmetry
        (1, 1) (2, 0) (sFifthMap x frame hu hv hr hs) =
      recoverPiece verticalSymmetry (1, 1)
            (makeMarkedPiece .y verticalSymmetry L (sV x.2.1)
            (part.seed_subset false (sFifthSystem_sV_mem x frame hu hv hr hs))
            (by simpa [L, BuiNeighborhood.pattern] using
              sFifth_left_y_occursAt x frame hu hv hr hs part)) ∪
      recoverPiece diagonalSymmetry (2, 0)
          (makeMarkedPiece .u diagonalSymmetry R (sR x.2.1)
            (part.seed_subset true (sFifthSystem_sR_mem x frame hu hv hr hs))
            (by simpa [R, BuiNeighborhood.pattern] using
              sFifth_right_u_occursAt x frame hu hv hr hs part)) by rfl]
    rw [hL, hR, ← Finset.image_union]
    congr 1
    calc
      L.cells ∪ R.cells = D.cells := hcoverD
      _ = (x.1.toPolyomino.cells.erase (sA x.2.1)).erase
          (sB x.2.1) := by
        simp only [D, sFifthSystem_cells, sdiff_pair_eq_erase_erase]
  rw [hrecover]
  change insert (0, 0) (insert (1, 0)
      (((x.1.toPolyomino.cells.erase (sA x.2.1)).erase (sB x.2.1)).image
        (fun c => -x.2.1 + c))) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + sA x.2.1 by
      apply Prod.ext <;> dsimp [sA, cellAt] <;> omega,
    show (1, 0) = -x.2.1 + sB x.2.1 by
      apply Prod.ext <;> dsimp [sB, cellAt] <;> omega]
  exact insert_two_image_erase _ (by simpa [sA] using frame.a_mem)
    (by simpa [sB] using frame.b_mem) (sA_ne_sB _) _

theorem sFifthMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .s n)
      (fx : SFrame x.1.toPolyomino.cells x.2.1)
      (fy : SFrame y.1.toPolyomino.cells y.2.1)
      (hux : sU x.2.1 ∈ x.1.toPolyomino.cells)
      (huy : sU y.2.1 ∈ y.1.toPolyomino.cells)
      (hvx : sV x.2.1 ∈ x.1.toPolyomino.cells)
      (hvy : sV y.2.1 ∈ y.1.toPolyomino.cells)
      (hrx : sR x.2.1 ∈ x.1.toPolyomino.cells)
      (hry : sR y.2.1 ∈ y.1.toPolyomino.cells)
      (hsx : sS x.2.1 ∈ x.1.toPolyomino.cells)
      (hsy : sS y.2.1 ∈ y.1.toPolyomino.cells),
      sFifthMap x fx hux hvx hrx hsx =
        sFifthMap y fy huy hvy hry hsy → x = y := by
  intro x y fx fy hux huy hvx hvy hrx hry hsx hsy hmap
  apply anchoredCells_injective .s n
  have h := congrArg
    (fun out : MarkedPair .y .u (n - 2) =>
      insert (0, 0) (insert (1, 0)
        (recoverMarkedPair verticalSymmetry diagonalSymmetry
          (1, 1) (2, 0) out))) hmap
  simpa [recoverFifthMap] using h

/-! ## The global five-way injection and the coefficient inequality -/

abbrev STarget (n : ℕ) :=
  Sum (MarkedOccurrence .g (n - 1))
    (Sum (MarkedPair .e .e (n - 1))
      (Sum (MarkedOccurrence .t (n - 2))
        (Sum (MarkedPair .x .g (n - 2))
          (MarkedPair .y .u (n - 2)))))

noncomputable def sMarkedMap (n : ℕ) :
    MarkedOccurrence .s n → STarget n := fun x => by
  let frame : SFrame x.1.toPolyomino.cells x.2.1 :=
    sFrame_of_occursAt (show buiSPattern.OccursAt
      x.1.toPolyomino.cells x.2.1 from marked_occursAt x)
  by_cases hu : sU x.2.1 ∈ x.1.toPolyomino.cells
  · by_cases hv : sV x.2.1 ∈ x.1.toPolyomino.cells
    · by_cases hr : sR x.2.1 ∈ x.1.toPolyomino.cells
      · by_cases hs : sS x.2.1 ∈ x.1.toPolyomino.cells
        · exact Sum.inr (Sum.inr (Sum.inr (Sum.inr
            (sFifthMap x frame hu hv hr hs))))
        · exact Sum.inr (Sum.inr (Sum.inr (Sum.inl
            (sFourthMap x frame hu hv hr hs))))
      · exact Sum.inr (Sum.inr (Sum.inl (sThirdMap x frame hu hv hr)))
    · exact Sum.inr (Sum.inl (sSecondMap x frame hu hv))
  · exact Sum.inl (sFirstMap x frame hu)

theorem sMarkedMap_injective (n : ℕ) :
    Function.Injective (sMarkedMap n) := by
  intro x y hxy
  let fx : SFrame x.1.toPolyomino.cells x.2.1 :=
    sFrame_of_occursAt (show buiSPattern.OccursAt
      x.1.toPolyomino.cells x.2.1 from marked_occursAt x)
  let fy : SFrame y.1.toPolyomino.cells y.2.1 :=
    sFrame_of_occursAt (show buiSPattern.OccursAt
      y.1.toPolyomino.cells y.2.1 from marked_occursAt y)
  by_cases hux : sU x.2.1 ∈ x.1.toPolyomino.cells
  · by_cases huy : sU y.2.1 ∈ y.1.toPolyomino.cells
    · by_cases hvx : sV x.2.1 ∈ x.1.toPolyomino.cells
      · by_cases hvy : sV y.2.1 ∈ y.1.toPolyomino.cells
        · by_cases hrx : sR x.2.1 ∈ x.1.toPolyomino.cells
          · by_cases hry : sR y.2.1 ∈ y.1.toPolyomino.cells
            · by_cases hsx : sS x.2.1 ∈ x.1.toPolyomino.cells
              · by_cases hsy : sS y.2.1 ∈ y.1.toPolyomino.cells
                · apply sFifthMap_injective n x y fx fy hux huy hvx hvy
                    hrx hry hsx hsy
                  simpa [sMarkedMap, fx, fy, hux, huy, hvx, hvy, hrx, hry,
                    hsx, hsy] using hxy
                · simp [sMarkedMap, fx, fy, hux, huy, hvx, hvy, hrx, hry,
                    hsx, hsy] at hxy
              · by_cases hsy : sS y.2.1 ∈ y.1.toPolyomino.cells
                · simp [sMarkedMap, fx, fy, hux, huy, hvx, hvy, hrx, hry,
                    hsx, hsy] at hxy
                · apply sFourthMap_injective n x y fx fy hux huy hvx hvy
                    hrx hry hsx hsy
                  simpa [sMarkedMap, fx, fy, hux, huy, hvx, hvy, hrx, hry,
                    hsx, hsy] using hxy
            · by_cases hsx : sS x.2.1 ∈ x.1.toPolyomino.cells
              <;> simp [sMarkedMap, fx, fy, hux, huy, hvx, hvy, hrx, hry,
                hsx] at hxy
          · by_cases hry : sR y.2.1 ∈ y.1.toPolyomino.cells
            · by_cases hsy : sS y.2.1 ∈ y.1.toPolyomino.cells
              <;> simp [sMarkedMap, fx, fy, hux, huy, hvx, hvy, hrx, hry,
                hsy] at hxy
            · apply sThirdMap_injective n x y fx fy hux huy hvx hvy hrx hry
              simpa [sMarkedMap, fx, fy, hux, huy, hvx, hvy, hrx, hry]
                using hxy
        · by_cases hrx : sR x.2.1 ∈ x.1.toPolyomino.cells
          · by_cases hsx : sS x.2.1 ∈ x.1.toPolyomino.cells
            <;> simp [sMarkedMap, fx, fy, hux, huy, hvx, hvy, hrx, hsx] at hxy
          · simp [sMarkedMap, fx, fy, hux, huy, hvx, hvy, hrx] at hxy
      · by_cases hvy : sV y.2.1 ∈ y.1.toPolyomino.cells
        · by_cases hry : sR y.2.1 ∈ y.1.toPolyomino.cells
          · by_cases hsy : sS y.2.1 ∈ y.1.toPolyomino.cells
            <;> simp [sMarkedMap, fx, fy, hux, huy, hvx, hvy, hry, hsy] at hxy
          · simp [sMarkedMap, fx, fy, hux, huy, hvx, hvy, hry] at hxy
        · apply sSecondMap_injective n x y fx fy hux huy hvx hvy
          simpa [sMarkedMap, fx, fy, hux, huy, hvx, hvy] using hxy
    · by_cases hvx : sV x.2.1 ∈ x.1.toPolyomino.cells
      · by_cases hrx : sR x.2.1 ∈ x.1.toPolyomino.cells
        · by_cases hsx : sS x.2.1 ∈ x.1.toPolyomino.cells
          <;> simp [sMarkedMap, fx, fy, hux, huy, hvx, hrx, hsx] at hxy
        · simp [sMarkedMap, fx, fy, hux, huy, hvx, hrx] at hxy
      · simp [sMarkedMap, fx, fy, hux, huy, hvx] at hxy
  · by_cases huy : sU y.2.1 ∈ y.1.toPolyomino.cells
    · by_cases hvy : sV y.2.1 ∈ y.1.toPolyomino.cells
      · by_cases hry : sR y.2.1 ∈ y.1.toPolyomino.cells
        · by_cases hsy : sS y.2.1 ∈ y.1.toPolyomino.cells
          <;> simp [sMarkedMap, fx, fy, hux, huy, hvy, hry, hsy] at hxy
        · simp [sMarkedMap, fx, fy, hux, huy, hvy, hry] at hxy
      · simp [sMarkedMap, fx, fy, hux, huy, hvy] at hxy
    · apply sFirstMap_injective n x y fx fy hux huy
      simpa [sMarkedMap, fx, fy, hux, huy] using hxy

theorem card_sTarget (n : ℕ) :
    Fintype.card (STarget n) =
      BuiNeighborhood.g.aggregateOccurrenceCount (n - 1) +
      aggregateConvolution .e .e (n - 1) +
      BuiNeighborhood.t.aggregateOccurrenceCount (n - 2) +
      aggregateConvolution .x .g (n - 2) +
      aggregateConvolution .y .u (n - 2) := by
  simp only [STarget, Fintype.card_sum, card_markedOccurrence,
    card_markedPair]
  omega

end GeometricFourFiveInternal

open GeometricFourFiveInternal

/-- The exact natural-number marked-occurrence form of Bui's `S` recurrence. -/
theorem buiS_aggregateOccurrenceCount_le (n : ℕ) :
    BuiNeighborhood.s.aggregateOccurrenceCount n ≤
      BuiNeighborhood.g.aggregateOccurrenceCount (n - 1) +
      aggregateConvolution .e .e (n - 1) +
      BuiNeighborhood.t.aggregateOccurrenceCount (n - 2) +
      aggregateConvolution .x .g (n - 2) +
      aggregateConvolution .y .u (n - 2) := by
  rw [← card_markedOccurrence, ← card_sTarget]
  exact Fintype.card_le_of_injective (sMarkedMap n) (sMarkedMap_injective n)

/-- The unconditional rational coefficient inequality for the actual
geometric `S` sequence. -/
theorem buiS_coefficient_le (n : ℕ) :
    BuiNeighborhood.s.coefficient n ≤
      BuiNeighborhood.g.coefficient (n - 1) +
      cauchyTwo BuiNeighborhood.e.coefficient BuiNeighborhood.e.coefficient (n - 1) +
      BuiNeighborhood.t.coefficient (n - 2) +
      cauchyTwo BuiNeighborhood.x.coefficient BuiNeighborhood.g.coefficient (n - 2) +
      cauchyTwo BuiNeighborhood.y.coefficient BuiNeighborhood.u.coefficient (n - 2) := by
  rw [cauchyTwo_coefficient_eq_aggregateConvolution,
    cauchyTwo_coefficient_eq_aggregateConvolution,
    cauchyTwo_coefficient_eq_aggregateConvolution]
  unfold BuiNeighborhood.coefficient
  exact_mod_cast buiS_aggregateOccurrenceCount_le n

/-- The `s` field required by `GeometricBuiGaps`, now discharged from finite
polyomino geometry rather than assumed. -/
theorem geometricCoefficientProfile_s_recurrence (n : ℕ) (_hn : 2 ≤ n) :
    geometricCoefficientProfile.s n ≤
      geometricCoefficientProfile.g (n - 1) +
      cauchyTwo geometricCoefficientProfile.e geometricCoefficientProfile.e (n - 1) +
      geometricCoefficientProfile.t (n - 2) +
      cauchyTwo geometricCoefficientProfile.x geometricCoefficientProfile.g (n - 2) +
      cauchyTwo geometricCoefficientProfile.y geometricCoefficientProfile.u (n - 2) := by
  simpa [geometricCoefficientProfile] using buiS_coefficient_le n

end LeanProofs.KlarnerConstant
