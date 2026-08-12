import KlarnerConstant.GeometricWCore

/-!
# Geometric W recurrence: seeded systems and deletion geometry

Internal definitions and lemmas used by the branch maps for the W recurrence.
-/

namespace LeanProofs.KlarnerConstant
namespace GeometricWInternal

/-! ## The three seeded systems used by the convolution branches -/

def wSecondSeeds (anchor : Cell) : Bool → Finset Cell
  | false => {wU anchor}
  | true => {wR anchor}

def wFourthSeeds (anchor : Cell) : Bool → Finset Cell
  | false => {wU anchor, wV anchor}
  | true => {wR anchor}

def wFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    Bool → Finset Cell
  | false => chainSeed cells (wU anchor) (wV anchor) (wTopV anchor)
  | true => chainSeed cells (wR anchor) (wS anchor) (wTopS anchor)

theorem wU_mem_wFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    wU anchor ∈ wFifthSeeds cells anchor false := by
  by_cases h : wTopV anchor ∈ cells <;>
    simp [wFifthSeeds, chainSeed, h]

theorem wV_mem_wFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    wV anchor ∈ wFifthSeeds cells anchor false := by
  by_cases h : wTopV anchor ∈ cells <;>
    simp [wFifthSeeds, chainSeed, h]

theorem wR_mem_wFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    wR anchor ∈ wFifthSeeds cells anchor true := by
  by_cases h : wTopS anchor ∈ cells <;>
    simp [wFifthSeeds, chainSeed, h]

theorem wS_mem_wFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    wS anchor ∈ wFifthSeeds cells anchor true := by
  by_cases h : wTopS anchor ∈ cells <;>
    simp [wFifthSeeds, chainSeed, h]

def wSecondSystem {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∉ x.1.toPolyomino.cells) : SeedSystem Bool := by
  let P := x.1.toPolyomino
  let anchor := x.2.1
  let deleted : Finset Cell := {wA anchor, wB anchor}
  let seeds := wSecondSeeds anchor
  refine deletionSeedSystem P deleted seeds ?_ ?_ ?_ ?_ (wU anchor) ?_ ?_
  · intro i
    cases i
    · intro c hc
      have hc' : c = wU anchor := by simpa [seeds, wSecondSeeds] using hc
      subst c
      exact Finset.mem_sdiff.mpr ⟨hu, by
        simp [deleted, wA, wU, wB, cellAt]⟩
    · intro c hc
      have hc' : c = wR anchor := by simpa [seeds, wSecondSeeds] using hc
      subst c
      exact Finset.mem_sdiff.mpr ⟨by simpa [P, anchor, wR] using frame.r_mem,
        by simp [deleted, wR, wA, wB, cellAt]⟩
  · intro i
    cases i <;> simp [seeds, wSecondSeeds]
  · intro i
    cases i <;> simp only [seeds, wSecondSeeds]
    <;> apply edgeConnected_singleton
  · apply Finset.disjoint_left.mpr
    intro c hc0 hc1
    simp only [seeds, wSecondSeeds, Finset.mem_singleton] at hc0 hc1
    subst c
    simp [wU, wR, cellAt] at hc1 <;> omega
  · simp [seeds, wSecondSeeds]
  · intro d c hd hc hcDeleted hadj
    have hseed := w_lowerDomino_boundary frame hd hc hcDeleted hadj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hseed
    rcases hseed with rfl | rfl | rfl
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor] using
        (show wU anchor ∈ seeds false by simp [seeds, wSecondSeeds])
    · exact (hv hc).elim
    · apply mem_coveredCells.mpr
      refine ⟨true, ?_⟩
      simpa only [anchor] using
        (show wR anchor ∈ seeds true by simp [seeds, wSecondSeeds])

def wFourthSystem {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells) : SeedSystem Bool := by
  let P := x.1.toPolyomino
  let anchor := x.2.1
  let deleted : Finset Cell := {wA anchor, wB anchor}
  let seeds := wFourthSeeds anchor
  refine deletionSeedSystem P deleted seeds ?_ ?_ ?_ ?_ (wU anchor) ?_ ?_
  · intro i
    cases i
    · intro c hc
      simp only [seeds, wFourthSeeds, Finset.mem_insert,
        Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact Finset.mem_sdiff.mpr ⟨hu, by
          simp [deleted, wA, wU, wB, cellAt]⟩
      · exact Finset.mem_sdiff.mpr ⟨hv, by
          simp [deleted, wV, wA, wB, cellAt]⟩
    · intro c hc
      have hc' : c = wR anchor := by simpa [seeds, wFourthSeeds] using hc
      subst c
      exact Finset.mem_sdiff.mpr ⟨hr, by
        simp [deleted, wR, wA, wB, cellAt]⟩
  · intro i
    cases i
    · exact ⟨wU anchor, by simp [seeds, wFourthSeeds]⟩
    · exact ⟨wR anchor, by simp [seeds, wFourthSeeds]⟩
  · intro i
    cases i
    · apply edgeConnected_pair
      simpa [wU, wV] using cellAt_east anchor 0 1
    · exact edgeConnected_singleton _
  · apply Finset.disjoint_left.mpr
    intro c hc0 hc1
    simp only [seeds, wFourthSeeds, Finset.mem_insert,
      Finset.mem_singleton] at hc0 hc1
    rcases hc0 with rfl | rfl
    <;> simp [wU, wV, wR, cellAt] at hc1 <;> omega
  · simp [seeds, wFourthSeeds]
  · intro d c hd hc hcDeleted hadj
    have hseed := w_lowerDomino_boundary frame hd hc hcDeleted hadj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hseed
    rcases hseed with rfl | rfl | rfl
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor] using
        (show wU anchor ∈ seeds false by simp [seeds, wFourthSeeds])
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor] using
        (show wV anchor ∈ seeds false by simp [seeds, wFourthSeeds])
    · apply mem_coveredCells.mpr
      refine ⟨true, ?_⟩
      simpa only [anchor] using
        (show wR anchor ∈ seeds true by simp [seeds, wFourthSeeds])

def wFifthSystem {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : wS x.2.1 ∈ x.1.toPolyomino.cells) : SeedSystem Bool := by
  let P := x.1.toPolyomino
  let anchor := x.2.1
  let deleted : Finset Cell := {wA anchor, wB anchor}
  let ambient := P.cells \ deleted
  let seeds := wFifthSeeds ambient anchor
  refine deletionSeedSystem P deleted seeds ?_ ?_ ?_ ?_ (wU anchor) ?_ ?_
  · intro i
    cases i
    · apply chainSeed_subset
      · exact Finset.mem_sdiff.mpr ⟨hu, by
          simp [deleted, wA, wU, wB, cellAt]⟩
      · exact Finset.mem_sdiff.mpr ⟨hv, by
          simp [deleted, wV, wA, wB, cellAt]⟩
    · apply chainSeed_subset
      · exact Finset.mem_sdiff.mpr ⟨hr, by
          simp [deleted, wR, wA, wB, cellAt]⟩
      · exact Finset.mem_sdiff.mpr ⟨hs, by
          simp [deleted, wS, wA, wB, cellAt]⟩
  · intro i
    cases i <;> apply chainSeed_nonempty
  · intro i
    cases i
    · apply chainSeed_connected
      · simpa [wU, wV] using cellAt_east anchor 0 1
      · simpa [wV, wTopV] using cellAt_north anchor 1 1
    · apply chainSeed_connected
      · simpa [wR, wS] using cellAt_north anchor 2 0
      · simpa [wS, wTopS] using cellAt_north anchor 2 1
  · apply Finset.disjoint_left.mpr
    intro c hc0 hc1
    have hc0' : c = wU anchor ∨ c = wV anchor ∨
        (c = wTopV anchor ∧ wTopV anchor ∈ ambient) := by
      exact (mem_chainSeed_iff.mp (show
        c ∈ chainSeed ambient (wU anchor) (wV anchor) (wTopV anchor) from hc0))
    have hc1' : c = wR anchor ∨ c = wS anchor ∨
        (c = wTopS anchor ∧ wTopS anchor ∈ ambient) := by
      exact (mem_chainSeed_iff.mp (show
        c ∈ chainSeed ambient (wR anchor) (wS anchor) (wTopS anchor) from hc1))
    rcases hc0' with h0 | h0 | ⟨h0, _⟩ <;>
      rcases hc1' with h1 | h1 | ⟨h1, _⟩ <;>
      have h := h0.symm.trans h1 <;>
      simp [wU, wV, wR, wS, wTopV, wTopS, cellAt] at h
  · simpa only [seeds] using wU_mem_wFifthSeeds ambient anchor
  · intro d c hd hc hcDeleted hadj
    have hseed := w_lowerDomino_boundary frame hd hc hcDeleted hadj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hseed
    rcases hseed with rfl | rfl | rfl
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor, seeds] using wU_mem_wFifthSeeds ambient anchor
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor, seeds] using wV_mem_wFifthSeeds ambient anchor
    · apply mem_coveredCells.mpr
      refine ⟨true, ?_⟩
      simpa only [anchor, seeds] using wR_mem_wFifthSeeds ambient anchor

/-! Stable projections of the seeded systems. -/

@[simp]
theorem wSecondSystem_cells {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∉ x.1.toPolyomino.cells) :
    (wSecondSystem x frame hu hv).cells =
      x.1.toPolyomino.cells \ {wA x.2.1, wB x.2.1} := by
  rfl

@[simp]
theorem wSecondSystem_seeds {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∉ x.1.toPolyomino.cells) (i : Bool) :
    (wSecondSystem x frame hu hv).seeds i = wSecondSeeds x.2.1 i := by
  rfl

@[simp]
theorem wFourthSystem_cells {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells) :
    (wFourthSystem x frame hu hv hr).cells =
      x.1.toPolyomino.cells \ {wA x.2.1, wB x.2.1} := by
  rfl

@[simp]
theorem wFourthSystem_seeds {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells) (i : Bool) :
    (wFourthSystem x frame hu hv hr).seeds i = wFourthSeeds x.2.1 i := by
  rfl

@[simp]
theorem wFifthSystem_cells {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : wS x.2.1 ∈ x.1.toPolyomino.cells) :
    (wFifthSystem x frame hu hv hr hs).cells =
      x.1.toPolyomino.cells \ {wA x.2.1, wB x.2.1} := by
  rfl

@[simp]
theorem wFifthSystem_seeds {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : wS x.2.1 ∈ x.1.toPolyomino.cells) (i : Bool) :
    (wFifthSystem x frame hu hv hr hs).seeds i =
      wFifthSeeds
        (x.1.toPolyomino.cells \ {wA x.2.1, wB x.2.1}) x.2.1 i := by
  rfl

theorem wFifthSystem_wU_mem {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : wS x.2.1 ∈ x.1.toPolyomino.cells) :
    wU x.2.1 ∈ (wFifthSystem x frame hu hv hr hs).seeds false := by
  rw [wFifthSystem_seeds]
  exact wU_mem_wFifthSeeds _ _

theorem wFifthSystem_wV_mem {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : wS x.2.1 ∈ x.1.toPolyomino.cells) :
    wV x.2.1 ∈ (wFifthSystem x frame hu hv hr hs).seeds false := by
  rw [wFifthSystem_seeds]
  exact wV_mem_wFifthSeeds _ _

theorem wFifthSystem_wR_mem {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : wS x.2.1 ∈ x.1.toPolyomino.cells) :
    wR x.2.1 ∈ (wFifthSystem x frame hu hv hr hs).seeds true := by
  rw [wFifthSystem_seeds]
  exact wR_mem_wFifthSeeds _ _

theorem wFifthSystem_wS_mem {n : ℕ} (x : MarkedOccurrence .w n)
    (frame : WFrame x.1.toPolyomino.cells x.2.1)
    (hu : wU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : wV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : wR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : wS x.2.1 ∈ x.1.toPolyomino.cells) :
    wS x.2.1 ∈ (wFifthSystem x frame hu hv hr hs).seeds true := by
  rw [wFifthSystem_seeds]
  exact wS_mem_wFifthSeeds _ _

/-! A specialized two-cell retraction for the third branch. -/

def retractLowerDomino (a b u v : Cell) (c : Cell) : Cell :=
  if c = a then u else if c = b then v else c

theorem edgeConnected_eraseLowerDomino (P : Polyomino)
    (a b u v : Cell) (ha : a ∈ P.cells) (hb : b ∈ P.cells)
    (hu : u ∈ P.cells) (hv : v ∈ P.cells)
    (hab : a ≠ b) (hau : a ≠ u) (hub : u ≠ b)
    (hva : v ≠ a) (hbv : b ≠ v)
    (huv : EdgeAdjacent u v)
    (haNeighbors : ∀ {c}, c ∈ P.cells → EdgeAdjacent a c →
      c = b ∨ c = u)
    (hbNeighbors : ∀ {c}, c ∈ P.cells → EdgeAdjacent b c →
      c = a ∨ c = v) :
    EdgeConnected ((P.cells.erase a).erase b) := by
  intro x hx y hy
  have hx0 := Finset.mem_erase.mp hx
  have hx1 := Finset.mem_erase.mp hx0.2
  have hy0 := Finset.mem_erase.mp hy
  have hy1 := Finset.mem_erase.mp hy0.2
  have huRemaining : u ∈ (P.cells.erase a).erase b :=
    Finset.mem_erase.mpr ⟨hub,
      Finset.mem_erase.mpr ⟨hau.symm, hu⟩⟩
  have hvRemaining : v ∈ (P.cells.erase a).erase b :=
    Finset.mem_erase.mpr ⟨hbv.symm,
      Finset.mem_erase.mpr ⟨hva, hv⟩⟩
  have huvRemaining : EdgeAdjacentIn ((P.cells.erase a).erase b) u v :=
    ⟨huRemaining, hvRemaining, huv⟩
  have mapEdge : ∀ {c d}, EdgeAdjacentIn P.cells c d →
      Relation.ReflTransGen (EdgeAdjacentIn ((P.cells.erase a).erase b))
        (retractLowerDomino a b u v c) (retractLowerDomino a b u v d) := by
    intro c d hcd
    by_cases hca : c = a
    · subst c
      rcases haNeighbors hcd.2.1 hcd.2.2 with hdb | hdu
      · simpa [retractLowerDomino, hdb, hab, hab.symm] using
          (Relation.ReflTransGen.single huvRemaining)
      · simpa [retractLowerDomino, hdu, hau, hau.symm, hub] using
          (Relation.ReflTransGen.refl :
            Relation.ReflTransGen (EdgeAdjacentIn ((P.cells.erase a).erase b)) u u)
    · by_cases hcb : c = b
      · subst c
        rcases hbNeighbors hcd.2.1 hcd.2.2 with hda | hdv
        · simpa [retractLowerDomino, hda, hab, hab.symm] using
            (Relation.ReflTransGen.single
              (edgeAdjacentIn_symm huvRemaining))
        · simpa [retractLowerDomino, hdv, hab.symm, hva, hbv, hbv.symm] using
            (Relation.ReflTransGen.refl :
              Relation.ReflTransGen (EdgeAdjacentIn ((P.cells.erase a).erase b)) v v)
      · by_cases hda : d = a
        · subst d
          have hc := haNeighbors hcd.1 (edgeAdjacent_symm hcd.2.2)
          rcases hc with hcb' | hcu
          · exact (hcb hcb').elim
          · simpa [retractLowerDomino, hcu, hca, hcb, hau, hau.symm, hub] using
              (Relation.ReflTransGen.refl :
                Relation.ReflTransGen (EdgeAdjacentIn ((P.cells.erase a).erase b)) u u)
        · by_cases hdb : d = b
          · subst d
            have hc := hbNeighbors hcd.1 (edgeAdjacent_symm hcd.2.2)
            rcases hc with hca' | hcv
            · exact (hca hca').elim
            · simpa [retractLowerDomino, hcv, hca, hcb, hab.symm, hva, hbv,
                hbv.symm] using
                (Relation.ReflTransGen.refl :
                  Relation.ReflTransGen (EdgeAdjacentIn ((P.cells.erase a).erase b)) v v)
          · apply Relation.ReflTransGen.single
            simpa [retractLowerDomino, hca, hcb, hda, hdb] using
              (show EdgeAdjacentIn ((P.cells.erase a).erase b) c d from
                ⟨by simp [hca, hcb, hcd.1], by simp [hda, hdb, hcd.2.1],
                  hcd.2.2⟩)
  have hpath := P.edgeConnected x hx1.2 y hy1.2
  have hlift := hpath.lift' (retractLowerDomino a b u v)
    (fun _ _ hstep => mapEdge hstep)
  change Relation.ReflTransGen (EdgeAdjacentIn ((P.cells.erase a).erase b))
    (retractLowerDomino a b u v x) (retractLowerDomino a b u v y) at hlift
  simpa [retractLowerDomino, hx1.1, hx0.1, hy1.1, hy0.1] using hlift

def retractLeaf (leaf parent c : Cell) : Cell :=
  if c = leaf then parent else c

theorem edgeConnected_eraseLeaf (P : Polyomino) (leaf parent : Cell)
    (hleaf : leaf ∈ P.cells) (hparent : parent ∈ P.cells)
    (hne : leaf ≠ parent)
    (honly : ∀ {c}, c ∈ P.cells → EdgeAdjacent leaf c → c = parent) :
    EdgeConnected (P.cells.erase leaf) := by
  intro x hx y hy
  have hx' := Finset.mem_erase.mp hx
  have hy' := Finset.mem_erase.mp hy
  have mapEdge : ∀ {c d}, EdgeAdjacentIn P.cells c d →
      Relation.ReflTransGen (EdgeAdjacentIn (P.cells.erase leaf))
        (retractLeaf leaf parent c) (retractLeaf leaf parent d) := by
    intro c d hcd
    by_cases hc : c = leaf
    · subst c
      have hd := honly hcd.2.1 hcd.2.2
      subst d
      simpa [retractLeaf, hne, hne.symm] using
        (Relation.ReflTransGen.refl :
          Relation.ReflTransGen (EdgeAdjacentIn (P.cells.erase leaf)) parent parent)
    · by_cases hd : d = leaf
      · subst d
        have hcparent := honly hcd.1 (edgeAdjacent_symm hcd.2.2)
        subst c
        simpa [retractLeaf, hne, hne.symm] using
          (Relation.ReflTransGen.refl :
            Relation.ReflTransGen (EdgeAdjacentIn (P.cells.erase leaf)) parent parent)
      · apply Relation.ReflTransGen.single
        simpa [retractLeaf, hc, hd] using
          (show EdgeAdjacentIn (P.cells.erase leaf) c d from
            ⟨Finset.mem_erase.mpr ⟨hc, hcd.1⟩,
              Finset.mem_erase.mpr ⟨hd, hcd.2.1⟩, hcd.2.2⟩)
  have hpath := P.edgeConnected x hx'.2 y hy'.2
  have hlift := hpath.lift' (retractLeaf leaf parent)
    (fun _ _ hstep => mapEdge hstep)
  change Relation.ReflTransGen (EdgeAdjacentIn (P.cells.erase leaf))
    (retractLeaf leaf parent x) (retractLeaf leaf parent y) at hlift
  simpa [retractLeaf, hx'.1, hy'.1] using hlift

def eraseLeafPolyomino (P : Polyomino) (leaf parent : Cell)
    (hleaf : leaf ∈ P.cells) (hparent : parent ∈ P.cells)
    (hne : leaf ≠ parent)
    (honly : ∀ {c}, c ∈ P.cells → EdgeAdjacent leaf c → c = parent) :
    Polyomino where
  cells := P.cells.erase leaf
  nonempty := ⟨parent, Finset.mem_erase.mpr ⟨hne.symm, hparent⟩⟩
  edgeConnected := edgeConnected_eraseLeaf P leaf parent hleaf hparent hne honly

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

/-! ## Exposed patterns on branch remainders -/

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

end GeometricWInternal
end LeanProofs.KlarnerConstant

