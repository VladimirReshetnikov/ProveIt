import KlarnerConstant.GeometricQGeometry

/-!
# Finite encoding and coefficient endpoint for the `Q` recurrence

This module encodes the five geometric branches in the shifted singleton and
two-factor convolution targets, proves injectivity by explicit reconstruction,
and exports the original public aggregate and coefficient recurrence theorems.
-/

namespace LeanProofs.KlarnerConstant
namespace QProof

/-! ## The five branch encoders -/

noncomputable def qFirstMap {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∉ x.1.toPolyomino.cells) :
    MarkedOccurrence .g (n - 1) := by
  let R := qFirstRemainder x frame hu
  have hcard : R.cells.card = n - 1 := by
    change (x.1.toPolyomino.cells.erase (qA x.2.1)).card = n - 1
    exact erase_one_card x.1 (by simpa [qA] using frame.a_mem)
  exact makeMarkedPieceOfCard .g diagonalSymmetry R (qB x.2.1)
    (by exact Finset.mem_erase.mpr ⟨(qA_ne_qB _).symm,
      by simpa [qB] using frame.b_mem⟩)
    (by simpa [R, BuiNeighborhood.pattern] using
      qFirst_g_occursAt x frame hu) hcard

noncomputable def qSecondMap {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∉ x.1.toPolyomino.cells) :
    MarkedPair .g .e (n - 1) := by
  let D := qSecondSystem x frame hu
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hsum : L.cells.card + R.cells.card = n - 1 := by
    calc
      L.cells.card + R.cells.card = D.cells.card := bool_partition_card part
      _ = n - 1 := by
        change (x.1.toPolyomino.cells \ {qA x.2.1}).card = n - 1
        rw [Finset.sdiff_singleton_eq_erase]
        exact erase_one_card x.1 (by simpa [qA] using frame.a_mem)
  refine ⟨⟨(L.cells.card, R.cells.card), ?_⟩, ?_, ?_⟩
  · exact Finset.HasAntidiagonal.mem_antidiagonal.mpr hsum
  · exact makeMarkedPiece .g verticalSymmetry L (qU x.2.1)
      (part.seed_subset false
        (by rw [qSecondSystem_seeds]; simp [qSecondSeeds]))
      (by simpa [L, BuiNeighborhood.pattern] using
        qSecond_left_g_occursAt x frame hu hv part)
  · exact makeMarkedPiece .e diagonalSymmetry R (qB x.2.1)
      (part.seed_subset true
        (by rw [qSecondSystem_seeds]; simp [qSecondSeeds]))
      (by simpa [R, BuiNeighborhood.pattern] using
        qSecond_right_e_occursAt x frame hu hv part)

noncomputable def qThirdMap {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∉ x.1.toPolyomino.cells) :
    MarkedOccurrence .u (n - 2) := by
  let R := qThirdRemainder x frame hu hv hr
  have hcard : R.cells.card = n - 2 := by
    change ((x.1.toPolyomino.cells.erase (qA x.2.1)).erase
      (qB x.2.1)).card = n - 2
    exact erase_two_card x.1 (by simpa [qA] using frame.a_mem)
      (by simpa [qB] using frame.b_mem) (qA_ne_qB _)
  exact makeMarkedPieceOfCard .u identitySymmetry R (qU x.2.1)
    (by simpa [R] using qThird_u_mem x frame hu hv hr)
    (by simpa [R, BuiNeighborhood.pattern] using
      qThird_u_occursAt x frame hu hv hr) hcard

noncomputable def qFourthMap {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : qS x.2.1 ∉ x.1.toPolyomino.cells) :
    MarkedPair .t .g (n - 2) := by
  let D := qFourthSystem x frame hu hv hr
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hsum : L.cells.card + R.cells.card = n - 2 := by
    calc
      L.cells.card + R.cells.card = D.cells.card := bool_partition_card part
      _ = n - 2 := by
        change (x.1.toPolyomino.cells \ {qA x.2.1, qB x.2.1}).card = n - 2
        rw [sdiff_pair_eq_erase_erase]
        exact erase_two_card x.1
          (by simpa [qA] using frame.a_mem)
          (by simpa [qB] using frame.b_mem) (qA_ne_qB _)
  refine ⟨⟨(L.cells.card, R.cells.card), ?_⟩, ?_, ?_⟩
  · exact Finset.HasAntidiagonal.mem_antidiagonal.mpr hsum
  · exact makeMarkedPiece .t verticalSymmetry L (qV x.2.1)
      (part.seed_subset false
        (by rw [qFourthSystem_seeds]; simp [qFourthSeeds]))
      (by simpa [L, BuiNeighborhood.pattern] using
        qFourth_left_t_occursAt x frame hu hv hr hs part)
  · exact makeMarkedPiece .g quarterTurnSymmetry R (qR x.2.1)
      (part.seed_subset true
        (by rw [qFourthSystem_seeds]; simp [qFourthSeeds]))
      (by simpa [R, BuiNeighborhood.pattern] using
        qFourth_right_g_occursAt x frame hu hv hr hs part)

noncomputable def qFifthMap {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : qS x.2.1 ∈ x.1.toPolyomino.cells) :
    MarkedPair .r .u (n - 2) := by
  let D := qFifthSystem x frame hu hv hr hs
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hsum : L.cells.card + R.cells.card = n - 2 := by
    calc
      L.cells.card + R.cells.card = D.cells.card := bool_partition_card part
      _ = n - 2 := by
        change (x.1.toPolyomino.cells \ {qA x.2.1, qB x.2.1}).card = n - 2
        rw [sdiff_pair_eq_erase_erase]
        exact erase_two_card x.1
          (by simpa [qA] using frame.a_mem)
          (by simpa [qB] using frame.b_mem) (qA_ne_qB _)
  refine ⟨⟨(L.cells.card, R.cells.card), ?_⟩, ?_, ?_⟩
  · exact Finset.HasAntidiagonal.mem_antidiagonal.mpr hsum
  · exact makeMarkedPiece .r verticalSymmetry L (qV x.2.1)
      (part.seed_subset false (qFifthSystem_qV_mem x frame hu hv hr hs))
      (by simpa [L, BuiNeighborhood.pattern] using
        qFifth_left_r_occursAt x frame hu hv hr hs part)
  · exact makeMarkedPiece .u diagonalSymmetry R (qR x.2.1)
      (part.seed_subset true (qFifthSystem_qR_mem x frame hu hv hr hs))
      (by simpa [R, BuiNeighborhood.pattern] using
        qFifth_right_u_occursAt x frame hu hv hr hs part)

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

theorem qFirst_reconstruct {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∉ x.1.toPolyomino.cells) :
    insert (0, 0) (recoverPiece diagonalSymmetry (1, 0)
      (qFirstMap x frame hu)) = anchoredCells x := by
  classical
  let R := qFirstRemainder x frame hu
  have hcard : R.cells.card = n - 1 := by
    change (x.1.toPolyomino.cells.erase (qA x.2.1)).card = n - 1
    exact erase_one_card x.1 (by simpa [qA] using frame.a_mem)
  have hrecover := recover_makeMarkedPieceOfCard .g diagonalSymmetry
    R x.2.1 (qB x.2.1) (1, 0)
    (by apply Prod.ext <;> dsimp [qB, cellAt] <;> omega)
    (by exact Finset.mem_erase.mpr ⟨(qA_ne_qB _).symm,
      by simpa [qB] using frame.b_mem⟩)
    (by simpa [R, BuiNeighborhood.pattern] using
      qFirst_g_occursAt x frame hu) hcard
  have hRcells : R.cells = x.1.toPolyomino.cells.erase (qA x.2.1) := rfl
  have hmap : recoverPiece diagonalSymmetry (1, 0) (qFirstMap x frame hu) =
      (x.1.toPolyomino.cells.erase (qA x.2.1)).image
        (fun c => -x.2.1 + c) := by
    calc
      _ = R.cells.image (fun c => -x.2.1 + c) := by
        simpa only [qFirstMap, R, qFirstRemainder] using hrecover
      _ = (x.1.toPolyomino.cells.erase (qA x.2.1)).image
          (fun c => -x.2.1 + c) := by rw [hRcells]
  rw [hmap]
  change insert (0, 0)
      ((x.1.toPolyomino.cells.erase (qA x.2.1)).image
        (fun c => -x.2.1 + c)) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + qA x.2.1 by
    apply Prod.ext <;> dsimp [qA, cellAt] <;> omega]
  exact insert_image_erase _ (by simpa [qA] using frame.a_mem) _

theorem qFirstMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .q n)
      (fx : QFrame x.1.toPolyomino.cells x.2.1)
      (fy : QFrame y.1.toPolyomino.cells y.2.1)
      (hx : qU x.2.1 ∉ x.1.toPolyomino.cells)
      (hy : qU y.2.1 ∉ y.1.toPolyomino.cells),
      qFirstMap x fx hx = qFirstMap y fy hy → x = y := by
  intro x y fx fy hx hy hmap
  apply anchoredCells_injective .q n
  have h := congrArg
    (fun out : MarkedOccurrence .g (n - 1) =>
      insert (0, 0) (recoverPiece diagonalSymmetry (1, 0) out)) hmap
  simpa [qFirst_reconstruct] using h

theorem recoverSecondMap {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∉ x.1.toPolyomino.cells) :
    insert (0, 0)
      (recoverMarkedPair verticalSymmetry diagonalSymmetry
        (0, 1) (1, 0) (qSecondMap x frame hu hv)) = anchoredCells x := by
  classical
  let D := qSecondSystem x frame hu
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hL := recover_makeMarkedPiece .g verticalSymmetry L x.2.1
    (qU x.2.1) (0, 1)
    (by apply Prod.ext <;> dsimp [qU, cellAt] <;> omega)
    (part.seed_subset false
      (by rw [qSecondSystem_seeds]; simp [qSecondSeeds]))
    (by simpa [L, BuiNeighborhood.pattern] using
      qSecond_left_g_occursAt x frame hu hv part)
  have hR := recover_makeMarkedPiece .e diagonalSymmetry R x.2.1
    (qB x.2.1) (1, 0)
    (by apply Prod.ext <;> dsimp [qB, cellAt] <;> omega)
    (part.seed_subset true
      (by rw [qSecondSystem_seeds]; simp [qSecondSeeds]))
    (by simpa [R, BuiNeighborhood.pattern] using
      qSecond_right_e_occursAt x frame hu hv part)
  have hcoverD : L.cells ∪ R.cells = D.cells := by
    change part.territories false ∪ part.territories true = D.cells
    rw [← part.cover]
    ext c
    simp [coveredCells, or_comm]
  have hrecover : recoverMarkedPair verticalSymmetry diagonalSymmetry
      (0, 1) (1, 0) (qSecondMap x frame hu hv) =
      (x.1.toPolyomino.cells.erase (qA x.2.1)).image
        (fun c => -x.2.1 + c) := by
    rw [show recoverMarkedPair verticalSymmetry diagonalSymmetry
        (0, 1) (1, 0) (qSecondMap x frame hu hv) =
      recoverPiece verticalSymmetry (0, 1)
          (makeMarkedPiece .g verticalSymmetry L (qU x.2.1)
            (part.seed_subset false
              (by rw [qSecondSystem_seeds]; simp [qSecondSeeds]))
            (by simpa [L, BuiNeighborhood.pattern] using
              qSecond_left_g_occursAt x frame hu hv part)) ∪
      recoverPiece diagonalSymmetry (1, 0)
          (makeMarkedPiece .e diagonalSymmetry R (qB x.2.1)
            (part.seed_subset true
              (by rw [qSecondSystem_seeds]; simp [qSecondSeeds]))
            (by simpa [R, BuiNeighborhood.pattern] using
              qSecond_right_e_occursAt x frame hu hv part)) by
        rfl]
    rw [hL, hR, ← Finset.image_union]
    congr 1
    calc
      L.cells ∪ R.cells = D.cells := hcoverD
      _ = x.1.toPolyomino.cells.erase (qA x.2.1) := by
        simp only [D, qSecondSystem_cells, Finset.sdiff_singleton_eq_erase]
  rw [hrecover]
  change insert (0, 0)
      ((x.1.toPolyomino.cells.erase (qA x.2.1)).image
        (fun c => -x.2.1 + c)) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + qA x.2.1 by
    apply Prod.ext <;> dsimp [qA, cellAt] <;> omega]
  exact insert_image_erase _ (by simpa [qA] using frame.a_mem) _

theorem qSecondMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .q n)
      (fx : QFrame x.1.toPolyomino.cells x.2.1)
      (fy : QFrame y.1.toPolyomino.cells y.2.1)
      (hux : qU x.2.1 ∈ x.1.toPolyomino.cells)
      (huy : qU y.2.1 ∈ y.1.toPolyomino.cells)
      (hvx : qV x.2.1 ∉ x.1.toPolyomino.cells)
      (hvy : qV y.2.1 ∉ y.1.toPolyomino.cells),
      qSecondMap x fx hux hvx = qSecondMap y fy huy hvy → x = y := by
  intro x y fx fy hux huy hvx hvy hmap
  apply anchoredCells_injective .q n
  have h := congrArg
    (fun out : MarkedPair .g .e (n - 1) =>
      insert (0, 0) (recoverMarkedPair verticalSymmetry diagonalSymmetry
        (0, 1) (1, 0) out)) hmap
  simpa [recoverSecondMap] using h

theorem recoverThirdMap {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∉ x.1.toPolyomino.cells) :
    insert (0, 0) (insert (1, 0)
      (recoverPiece identitySymmetry (0, 1) (qThirdMap x frame hu hv hr))) =
      anchoredCells x := by
  classical
  let R := qThirdRemainder x frame hu hv hr
  have hcard : R.cells.card = n - 2 := by
    change ((x.1.toPolyomino.cells.erase (qA x.2.1)).erase
      (qB x.2.1)).card = n - 2
    exact erase_two_card x.1 (by simpa [qA] using frame.a_mem)
      (by simpa [qB] using frame.b_mem) (qA_ne_qB _)
  have hrecover := recover_makeMarkedPieceOfCard .u identitySymmetry R x.2.1
    (qU x.2.1) (0, 1)
    (by apply Prod.ext <;> dsimp [qU, cellAt] <;> omega)
    (by simpa [R] using qThird_u_mem x frame hu hv hr)
    (by simpa [R, BuiNeighborhood.pattern] using
      qThird_u_occursAt x frame hu hv hr) hcard
  have hRcells : R.cells =
      (x.1.toPolyomino.cells.erase (qA x.2.1)).erase (qB x.2.1) := rfl
  have hmap : recoverPiece identitySymmetry (0, 1)
      (qThirdMap x frame hu hv hr) =
      ((x.1.toPolyomino.cells.erase (qA x.2.1)).erase (qB x.2.1)).image
        (fun c => -x.2.1 + c) := by
    calc
      _ = R.cells.image (fun c => -x.2.1 + c) := by
        simpa only [qThirdMap, R, qThirdRemainder] using hrecover
      _ = ((x.1.toPolyomino.cells.erase (qA x.2.1)).erase
          (qB x.2.1)).image (fun c => -x.2.1 + c) := by rw [hRcells]
  rw [hmap]
  change insert (0, 0) (insert (1, 0)
      (((x.1.toPolyomino.cells.erase (qA x.2.1)).erase (qB x.2.1)).image
        (fun c => -x.2.1 + c))) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + qA x.2.1 by
      apply Prod.ext <;> dsimp [qA, cellAt] <;> omega,
    show (1, 0) = -x.2.1 + qB x.2.1 by
      apply Prod.ext <;> dsimp [qB, cellAt] <;> omega]
  exact insert_two_image_erase _ (by simpa [qA] using frame.a_mem)
    (by simpa [qB] using frame.b_mem) (qA_ne_qB _) _

theorem qThirdMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .q n)
      (fx : QFrame x.1.toPolyomino.cells x.2.1)
      (fy : QFrame y.1.toPolyomino.cells y.2.1)
      (hux : qU x.2.1 ∈ x.1.toPolyomino.cells)
      (huy : qU y.2.1 ∈ y.1.toPolyomino.cells)
      (hvx : qV x.2.1 ∈ x.1.toPolyomino.cells)
      (hvy : qV y.2.1 ∈ y.1.toPolyomino.cells)
      (hrx : qR x.2.1 ∉ x.1.toPolyomino.cells)
      (hry : qR y.2.1 ∉ y.1.toPolyomino.cells),
      qThirdMap x fx hux hvx hrx = qThirdMap y fy huy hvy hry → x = y := by
  intro x y fx fy hux huy hvx hvy hrx hry hmap
  apply anchoredCells_injective .q n
  have h := congrArg
    (fun out : MarkedOccurrence .u (n - 2) =>
      insert (0, 0) (insert (1, 0)
        (recoverPiece identitySymmetry (0, 1) out))) hmap
  simpa [recoverThirdMap] using h

theorem recoverFourthMap {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : qS x.2.1 ∉ x.1.toPolyomino.cells) :
    insert (0, 0) (insert (1, 0)
      (recoverMarkedPair verticalSymmetry quarterTurnSymmetry
        (1, 1) (2, 0) (qFourthMap x frame hu hv hr hs))) = anchoredCells x := by
  classical
  let D := qFourthSystem x frame hu hv hr
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hL := recover_makeMarkedPiece .t verticalSymmetry L x.2.1
    (qV x.2.1) (1, 1)
    (by apply Prod.ext <;> dsimp [qV, cellAt] <;> omega)
    (part.seed_subset false
      (by rw [qFourthSystem_seeds]; simp [qFourthSeeds]))
    (by simpa [L, BuiNeighborhood.pattern] using
      qFourth_left_t_occursAt x frame hu hv hr hs part)
  have hR := recover_makeMarkedPiece .g quarterTurnSymmetry R x.2.1
    (qR x.2.1) (2, 0)
    (by apply Prod.ext <;> dsimp [qR, cellAt] <;> omega)
    (part.seed_subset true
      (by rw [qFourthSystem_seeds]; simp [qFourthSeeds]))
    (by simpa [R, BuiNeighborhood.pattern] using
      qFourth_right_g_occursAt x frame hu hv hr hs part)
  have hcoverD : L.cells ∪ R.cells = D.cells := by
    change part.territories false ∪ part.territories true = D.cells
    rw [← part.cover]
    ext c
    simp [coveredCells, or_comm]
  have hrecover : recoverMarkedPair verticalSymmetry quarterTurnSymmetry
      (1, 1) (2, 0) (qFourthMap x frame hu hv hr hs) =
      ((x.1.toPolyomino.cells.erase (qA x.2.1)).erase (qB x.2.1)).image
        (fun c => -x.2.1 + c) := by
    rw [show recoverMarkedPair verticalSymmetry quarterTurnSymmetry
        (1, 1) (2, 0) (qFourthMap x frame hu hv hr hs) =
      recoverPiece verticalSymmetry (1, 1)
          (makeMarkedPiece .t verticalSymmetry L (qV x.2.1)
            (part.seed_subset false
              (by rw [qFourthSystem_seeds]; simp [qFourthSeeds]))
            (by simpa [L, BuiNeighborhood.pattern] using
              qFourth_left_t_occursAt x frame hu hv hr hs part)) ∪
      recoverPiece quarterTurnSymmetry (2, 0)
          (makeMarkedPiece .g quarterTurnSymmetry R (qR x.2.1)
            (part.seed_subset true
              (by rw [qFourthSystem_seeds]; simp [qFourthSeeds]))
            (by simpa [R, BuiNeighborhood.pattern] using
              qFourth_right_g_occursAt x frame hu hv hr hs part)) by rfl]
    rw [hL, hR, ← Finset.image_union]
    congr 1
    calc
      L.cells ∪ R.cells = D.cells := hcoverD
      _ = (x.1.toPolyomino.cells.erase (qA x.2.1)).erase
          (qB x.2.1) := by
        simp only [D, qFourthSystem_cells, sdiff_pair_eq_erase_erase]
  rw [hrecover]
  change insert (0, 0) (insert (1, 0)
      (((x.1.toPolyomino.cells.erase (qA x.2.1)).erase (qB x.2.1)).image
        (fun c => -x.2.1 + c))) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + qA x.2.1 by
      apply Prod.ext <;> dsimp [qA, cellAt] <;> omega,
    show (1, 0) = -x.2.1 + qB x.2.1 by
      apply Prod.ext <;> dsimp [qB, cellAt] <;> omega]
  exact insert_two_image_erase _ (by simpa [qA] using frame.a_mem)
    (by simpa [qB] using frame.b_mem) (qA_ne_qB _) _

theorem qFourthMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .q n)
      (fx : QFrame x.1.toPolyomino.cells x.2.1)
      (fy : QFrame y.1.toPolyomino.cells y.2.1)
      (hux : qU x.2.1 ∈ x.1.toPolyomino.cells)
      (huy : qU y.2.1 ∈ y.1.toPolyomino.cells)
      (hvx : qV x.2.1 ∈ x.1.toPolyomino.cells)
      (hvy : qV y.2.1 ∈ y.1.toPolyomino.cells)
      (hrx : qR x.2.1 ∈ x.1.toPolyomino.cells)
      (hry : qR y.2.1 ∈ y.1.toPolyomino.cells)
      (hsx : qS x.2.1 ∉ x.1.toPolyomino.cells)
      (hsy : qS y.2.1 ∉ y.1.toPolyomino.cells),
      qFourthMap x fx hux hvx hrx hsx =
        qFourthMap y fy huy hvy hry hsy → x = y := by
  intro x y fx fy hux huy hvx hvy hrx hry hsx hsy hmap
  apply anchoredCells_injective .q n
  have h := congrArg
    (fun out : MarkedPair .t .g (n - 2) =>
      insert (0, 0) (insert (1, 0)
        (recoverMarkedPair verticalSymmetry quarterTurnSymmetry
          (1, 1) (2, 0) out))) hmap
  simpa [recoverFourthMap] using h

theorem recoverFifthMap {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : qS x.2.1 ∈ x.1.toPolyomino.cells) :
    insert (0, 0) (insert (1, 0)
      (recoverMarkedPair verticalSymmetry diagonalSymmetry
        (1, 1) (2, 0) (qFifthMap x frame hu hv hr hs))) = anchoredCells x := by
  classical
  let D := qFifthSystem x frame hu hv hr hs
  let part := D.choosePartition
  let L := part.territoryPolyomino false
  let R := part.territoryPolyomino true
  have hL := recover_makeMarkedPiece .r verticalSymmetry L x.2.1
    (qV x.2.1) (1, 1)
    (by apply Prod.ext <;> dsimp [qV, cellAt] <;> omega)
    (part.seed_subset false (qFifthSystem_qV_mem x frame hu hv hr hs))
    (by simpa [L, BuiNeighborhood.pattern] using
      qFifth_left_r_occursAt x frame hu hv hr hs part)
  have hR := recover_makeMarkedPiece .u diagonalSymmetry R x.2.1
    (qR x.2.1) (2, 0)
    (by apply Prod.ext <;> dsimp [qR, cellAt] <;> omega)
    (part.seed_subset true (qFifthSystem_qR_mem x frame hu hv hr hs))
    (by simpa [R, BuiNeighborhood.pattern] using
      qFifth_right_u_occursAt x frame hu hv hr hs part)
  have hcoverD : L.cells ∪ R.cells = D.cells := by
    change part.territories false ∪ part.territories true = D.cells
    rw [← part.cover]
    ext c
    simp [coveredCells, or_comm]
  have hrecover : recoverMarkedPair verticalSymmetry diagonalSymmetry
      (1, 1) (2, 0) (qFifthMap x frame hu hv hr hs) =
      ((x.1.toPolyomino.cells.erase (qA x.2.1)).erase (qB x.2.1)).image
        (fun c => -x.2.1 + c) := by
    rw [show recoverMarkedPair verticalSymmetry diagonalSymmetry
        (1, 1) (2, 0) (qFifthMap x frame hu hv hr hs) =
      recoverPiece verticalSymmetry (1, 1)
          (makeMarkedPiece .r verticalSymmetry L (qV x.2.1)
            (part.seed_subset false (qFifthSystem_qV_mem x frame hu hv hr hs))
            (by simpa [L, BuiNeighborhood.pattern] using
              qFifth_left_r_occursAt x frame hu hv hr hs part)) ∪
      recoverPiece diagonalSymmetry (2, 0)
          (makeMarkedPiece .u diagonalSymmetry R (qR x.2.1)
            (part.seed_subset true (qFifthSystem_qR_mem x frame hu hv hr hs))
            (by simpa [R, BuiNeighborhood.pattern] using
              qFifth_right_u_occursAt x frame hu hv hr hs part)) by rfl]
    rw [hL, hR, ← Finset.image_union]
    congr 1
    calc
      L.cells ∪ R.cells = D.cells := hcoverD
      _ = (x.1.toPolyomino.cells.erase (qA x.2.1)).erase
          (qB x.2.1) := by
        simp only [D, qFifthSystem_cells, sdiff_pair_eq_erase_erase]
  rw [hrecover]
  change insert (0, 0) (insert (1, 0)
      (((x.1.toPolyomino.cells.erase (qA x.2.1)).erase (qB x.2.1)).image
        (fun c => -x.2.1 + c))) =
    x.1.toPolyomino.cells.image (fun c => -x.2.1 + c)
  rw [show (0, 0) = -x.2.1 + qA x.2.1 by
      apply Prod.ext <;> dsimp [qA, cellAt] <;> omega,
    show (1, 0) = -x.2.1 + qB x.2.1 by
      apply Prod.ext <;> dsimp [qB, cellAt] <;> omega]
  exact insert_two_image_erase _ (by simpa [qA] using frame.a_mem)
    (by simpa [qB] using frame.b_mem) (qA_ne_qB _) _

theorem qFifthMap_injective (n : ℕ) :
    ∀ (x y : MarkedOccurrence .q n)
      (fx : QFrame x.1.toPolyomino.cells x.2.1)
      (fy : QFrame y.1.toPolyomino.cells y.2.1)
      (hux : qU x.2.1 ∈ x.1.toPolyomino.cells)
      (huy : qU y.2.1 ∈ y.1.toPolyomino.cells)
      (hvx : qV x.2.1 ∈ x.1.toPolyomino.cells)
      (hvy : qV y.2.1 ∈ y.1.toPolyomino.cells)
      (hrx : qR x.2.1 ∈ x.1.toPolyomino.cells)
      (hry : qR y.2.1 ∈ y.1.toPolyomino.cells)
      (hsx : qS x.2.1 ∈ x.1.toPolyomino.cells)
      (hsy : qS y.2.1 ∈ y.1.toPolyomino.cells),
      qFifthMap x fx hux hvx hrx hsx =
        qFifthMap y fy huy hvy hry hsy → x = y := by
  intro x y fx fy hux huy hvx hvy hrx hry hsx hsy hmap
  apply anchoredCells_injective .q n
  have h := congrArg
    (fun out : MarkedPair .r .u (n - 2) =>
      insert (0, 0) (insert (1, 0)
        (recoverMarkedPair verticalSymmetry diagonalSymmetry
          (1, 1) (2, 0) out))) hmap
  simpa [recoverFifthMap] using h

/-! ## The global five-way injection and the coefficient inequality -/

abbrev QTarget (n : ℕ) :=
  Sum (MarkedOccurrence .g (n - 1))
    (Sum (MarkedPair .g .e (n - 1))
      (Sum (MarkedOccurrence .u (n - 2))
        (Sum (MarkedPair .t .g (n - 2))
          (MarkedPair .r .u (n - 2)))))

noncomputable def qMarkedMap (n : ℕ) :
    MarkedOccurrence .q n → QTarget n := fun x => by
  let frame : QFrame x.1.toPolyomino.cells x.2.1 :=
    qFrame_of_occursAt (show buiQPattern.OccursAt
      x.1.toPolyomino.cells x.2.1 from marked_occursAt x)
  by_cases hu : qU x.2.1 ∈ x.1.toPolyomino.cells
  · by_cases hv : qV x.2.1 ∈ x.1.toPolyomino.cells
    · by_cases hr : qR x.2.1 ∈ x.1.toPolyomino.cells
      · by_cases hs : qS x.2.1 ∈ x.1.toPolyomino.cells
        · exact Sum.inr (Sum.inr (Sum.inr (Sum.inr
            (qFifthMap x frame hu hv hr hs))))
        · exact Sum.inr (Sum.inr (Sum.inr (Sum.inl
            (qFourthMap x frame hu hv hr hs))))
      · exact Sum.inr (Sum.inr (Sum.inl (qThirdMap x frame hu hv hr)))
    · exact Sum.inr (Sum.inl (qSecondMap x frame hu hv))
  · exact Sum.inl (qFirstMap x frame hu)

theorem qMarkedMap_injective (n : ℕ) :
    Function.Injective (qMarkedMap n) := by
  intro x y hxy
  let fx : QFrame x.1.toPolyomino.cells x.2.1 :=
    qFrame_of_occursAt (show buiQPattern.OccursAt
      x.1.toPolyomino.cells x.2.1 from marked_occursAt x)
  let fy : QFrame y.1.toPolyomino.cells y.2.1 :=
    qFrame_of_occursAt (show buiQPattern.OccursAt
      y.1.toPolyomino.cells y.2.1 from marked_occursAt y)
  by_cases hux : qU x.2.1 ∈ x.1.toPolyomino.cells
  · by_cases huy : qU y.2.1 ∈ y.1.toPolyomino.cells
    · by_cases hvx : qV x.2.1 ∈ x.1.toPolyomino.cells
      · by_cases hvy : qV y.2.1 ∈ y.1.toPolyomino.cells
        · by_cases hrx : qR x.2.1 ∈ x.1.toPolyomino.cells
          · by_cases hry : qR y.2.1 ∈ y.1.toPolyomino.cells
            · by_cases hsx : qS x.2.1 ∈ x.1.toPolyomino.cells
              · by_cases hsy : qS y.2.1 ∈ y.1.toPolyomino.cells
                · apply qFifthMap_injective n x y fx fy hux huy hvx hvy
                    hrx hry hsx hsy
                  simpa [qMarkedMap, fx, fy, hux, huy, hvx, hvy, hrx, hry,
                    hsx, hsy] using hxy
                · simp [qMarkedMap, fx, fy, hux, huy, hvx, hvy, hrx, hry,
                    hsx, hsy] at hxy
              · by_cases hsy : qS y.2.1 ∈ y.1.toPolyomino.cells
                · simp [qMarkedMap, fx, fy, hux, huy, hvx, hvy, hrx, hry,
                    hsx, hsy] at hxy
                · apply qFourthMap_injective n x y fx fy hux huy hvx hvy
                    hrx hry hsx hsy
                  simpa [qMarkedMap, fx, fy, hux, huy, hvx, hvy, hrx, hry,
                    hsx, hsy] using hxy
            · by_cases hsx : qS x.2.1 ∈ x.1.toPolyomino.cells <;>
                simp [qMarkedMap, fx, fy, hux, huy, hvx, hvy, hrx, hry,
                  hsx] at hxy
          · by_cases hry : qR y.2.1 ∈ y.1.toPolyomino.cells
            · by_cases hsy : qS y.2.1 ∈ y.1.toPolyomino.cells <;>
                simp [qMarkedMap, fx, fy, hux, huy, hvx, hvy, hrx, hry,
                  hsy] at hxy
            · apply qThirdMap_injective n x y fx fy hux huy hvx hvy hrx hry
              simpa [qMarkedMap, fx, fy, hux, huy, hvx, hvy, hrx, hry]
                using hxy
        · by_cases hrx : qR x.2.1 ∈ x.1.toPolyomino.cells
          · by_cases hsx : qS x.2.1 ∈ x.1.toPolyomino.cells <;>
              simp [qMarkedMap, fx, fy, hux, huy, hvx, hvy, hrx, hsx] at hxy
          · simp [qMarkedMap, fx, fy, hux, huy, hvx, hvy, hrx] at hxy
      · by_cases hvy : qV y.2.1 ∈ y.1.toPolyomino.cells
        · by_cases hry : qR y.2.1 ∈ y.1.toPolyomino.cells
          · by_cases hsy : qS y.2.1 ∈ y.1.toPolyomino.cells <;>
              simp [qMarkedMap, fx, fy, hux, huy, hvx, hvy, hry, hsy] at hxy
          · simp [qMarkedMap, fx, fy, hux, huy, hvx, hvy, hry] at hxy
        · apply qSecondMap_injective n x y fx fy hux huy hvx hvy
          simpa [qMarkedMap, fx, fy, hux, huy, hvx, hvy] using hxy
    · by_cases hvx : qV x.2.1 ∈ x.1.toPolyomino.cells
      · by_cases hrx : qR x.2.1 ∈ x.1.toPolyomino.cells
        · by_cases hsx : qS x.2.1 ∈ x.1.toPolyomino.cells <;>
            simp [qMarkedMap, fx, fy, hux, huy, hvx, hrx, hsx] at hxy
        · simp [qMarkedMap, fx, fy, hux, huy, hvx, hrx] at hxy
      · simp [qMarkedMap, fx, fy, hux, huy, hvx] at hxy
  · by_cases huy : qU y.2.1 ∈ y.1.toPolyomino.cells
    · by_cases hvy : qV y.2.1 ∈ y.1.toPolyomino.cells
      · by_cases hry : qR y.2.1 ∈ y.1.toPolyomino.cells
        · by_cases hsy : qS y.2.1 ∈ y.1.toPolyomino.cells <;>
            simp [qMarkedMap, fx, fy, hux, huy, hvy, hry, hsy] at hxy
        · simp [qMarkedMap, fx, fy, hux, huy, hvy, hry] at hxy
      · simp [qMarkedMap, fx, fy, hux, huy, hvy] at hxy
    · apply qFirstMap_injective n x y fx fy hux huy
      simpa [qMarkedMap, fx, fy, hux, huy] using hxy

theorem card_qTarget (n : ℕ) :
    Fintype.card (QTarget n) =
      BuiNeighborhood.g.aggregateOccurrenceCount (n - 1) +
      aggregateConvolution .g .e (n - 1) +
      BuiNeighborhood.u.aggregateOccurrenceCount (n - 2) +
      aggregateConvolution .t .g (n - 2) +
      aggregateConvolution .r .u (n - 2) := by
  simp only [QTarget, Fintype.card_sum, card_markedOccurrence,
    card_markedPair]
  omega

end QProof

open QProof

/-- The exact natural-number marked-occurrence form of Bui's `Q` recurrence. -/
theorem buiQ_aggregateOccurrenceCount_le (n : ℕ) :
    BuiNeighborhood.q.aggregateOccurrenceCount n ≤
      BuiNeighborhood.g.aggregateOccurrenceCount (n - 1) +
      aggregateConvolution .g .e (n - 1) +
      BuiNeighborhood.u.aggregateOccurrenceCount (n - 2) +
      aggregateConvolution .t .g (n - 2) +
      aggregateConvolution .r .u (n - 2) := by
  rw [← card_markedOccurrence, ← card_qTarget]
  exact Fintype.card_le_of_injective (qMarkedMap n) (qMarkedMap_injective n)

/-- The unconditional rational coefficient inequality for the actual
geometric `Q` sequence. -/
theorem buiQ_coefficient_le (n : ℕ) :
    BuiNeighborhood.q.coefficient n ≤
      BuiNeighborhood.g.coefficient (n - 1) +
      cauchyTwo BuiNeighborhood.g.coefficient BuiNeighborhood.e.coefficient (n - 1) +
      BuiNeighborhood.u.coefficient (n - 2) +
      cauchyTwo BuiNeighborhood.t.coefficient BuiNeighborhood.g.coefficient (n - 2) +
      cauchyTwo BuiNeighborhood.r.coefficient BuiNeighborhood.u.coefficient (n - 2) := by
  rw [cauchyTwo_coefficient_eq_aggregateConvolution,
    cauchyTwo_coefficient_eq_aggregateConvolution,
    cauchyTwo_coefficient_eq_aggregateConvolution]
  unfold BuiNeighborhood.coefficient
  exact_mod_cast buiQ_aggregateOccurrenceCount_le n

/-- The `q` field required by `GeometricBuiGaps`, now discharged from finite
polyomino geometry rather than assumed. -/
theorem geometricCoefficientProfile_q_recurrence (n : ℕ) (_hn : 2 ≤ n) :
    geometricCoefficientProfile.q n ≤
      geometricCoefficientProfile.g (n - 1) +
      cauchyTwo geometricCoefficientProfile.g geometricCoefficientProfile.e (n - 1) +
      geometricCoefficientProfile.u (n - 2) +
      cauchyTwo geometricCoefficientProfile.t geometricCoefficientProfile.g (n - 2) +
      cauchyTwo geometricCoefficientProfile.r geometricCoefficientProfile.u (n - 2) := by
  simpa [geometricCoefficientProfile] using buiQ_coefficient_le n


end LeanProofs.KlarnerConstant
