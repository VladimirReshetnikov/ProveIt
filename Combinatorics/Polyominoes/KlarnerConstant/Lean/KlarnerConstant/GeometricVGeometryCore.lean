import KlarnerConstant.GeometricVCore

/-!
# Seeded decomposition systems for the four-branch `V` recurrence

This module constructs the three seeded systems and proves the deletion and
cardinality infrastructure used by the exposed branch geometry.
-/

namespace LeanProofs.KlarnerConstant
namespace GeometricVInternal

/-! ## The three seeded systems used by the convolution branches -/

def vSecondSeeds (anchor : Cell) : Bool → Finset Cell
  | false => {vU anchor}
  | true => {vR anchor}

def vFourthSeeds (anchor : Cell) : Bool → Finset Cell
  | false => {vU anchor, vV anchor}
  | true => {vR anchor}

def vFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    Bool → Finset Cell
  | false => chainSeed cells (vU anchor) (vV anchor) (vTopV anchor)
  | true => chainSeed cells (vR anchor) (vS anchor) (vTopS anchor)

theorem vU_mem_vFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    vU anchor ∈ vFifthSeeds cells anchor false := by
  by_cases h : vTopV anchor ∈ cells <;>
    simp [vFifthSeeds, chainSeed, h]

theorem vV_mem_vFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    vV anchor ∈ vFifthSeeds cells anchor false := by
  by_cases h : vTopV anchor ∈ cells <;>
    simp [vFifthSeeds, chainSeed, h]

theorem vR_mem_vFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    vR anchor ∈ vFifthSeeds cells anchor true := by
  by_cases h : vTopS anchor ∈ cells <;>
    simp [vFifthSeeds, chainSeed, h]

theorem vS_mem_vFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    vS anchor ∈ vFifthSeeds cells anchor true := by
  by_cases h : vTopS anchor ∈ cells <;>
    simp [vFifthSeeds, chainSeed, h]

def vSecondSystem {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∉ x.1.toPolyomino.cells) : SeedSystem Bool := by
  let P := x.1.toPolyomino
  let anchor := x.2.1
  let deleted : Finset Cell := {vA anchor, vB anchor}
  let seeds := vSecondSeeds anchor
  refine deletionSeedSystem P deleted seeds ?_ ?_ ?_ ?_ (vU anchor) ?_ ?_
  · intro i
    cases i
    · intro c hc
      have hc' : c = vU anchor := by simpa [seeds, vSecondSeeds] using hc
      subst c
      exact Finset.mem_sdiff.mpr ⟨hu, by
        simp [deleted, vA, vU, vB, cellAt]⟩
    · intro c hc
      have hc' : c = vR anchor := by simpa [seeds, vSecondSeeds] using hc
      subst c
      exact Finset.mem_sdiff.mpr ⟨by simpa [P, anchor, vR] using frame.r_mem,
        by simp [deleted, vR, vA, vB, cellAt]⟩
  · intro i
    cases i <;> simp [seeds, vSecondSeeds]
  · intro i
    cases i <;> simp only [seeds, vSecondSeeds]
    <;> apply edgeConnected_singleton
  · apply Finset.disjoint_left.mpr
    intro c hc0 hc1
    simp only [seeds, vSecondSeeds, Finset.mem_singleton] at hc0 hc1
    subst c
    simp [vU, vR, cellAt] at hc1 <;> omega
  · simp [seeds, vSecondSeeds]
  · intro d c hd hc hcDeleted hadj
    have hseed := v_lowerDomino_boundary frame hd hc hcDeleted hadj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hseed
    rcases hseed with rfl | rfl | rfl
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor] using
        (show vU anchor ∈ seeds false by simp [seeds, vSecondSeeds])
    · exact (hv hc).elim
    · apply mem_coveredCells.mpr
      refine ⟨true, ?_⟩
      simpa only [anchor] using
        (show vR anchor ∈ seeds true by simp [seeds, vSecondSeeds])

def vFourthSystem {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells) : SeedSystem Bool := by
  let P := x.1.toPolyomino
  let anchor := x.2.1
  let deleted : Finset Cell := {vA anchor, vB anchor}
  let seeds := vFourthSeeds anchor
  refine deletionSeedSystem P deleted seeds ?_ ?_ ?_ ?_ (vU anchor) ?_ ?_
  · intro i
    cases i
    · intro c hc
      simp only [seeds, vFourthSeeds, Finset.mem_insert,
        Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact Finset.mem_sdiff.mpr ⟨hu, by
          simp [deleted, vA, vU, vB, cellAt]⟩
      · exact Finset.mem_sdiff.mpr ⟨hv, by
          simp [deleted, vV, vA, vB, cellAt]⟩
    · intro c hc
      have hc' : c = vR anchor := by simpa [seeds, vFourthSeeds] using hc
      subst c
      exact Finset.mem_sdiff.mpr ⟨hr, by
        simp [deleted, vR, vA, vB, cellAt]⟩
  · intro i
    cases i
    · exact ⟨vU anchor, by simp [seeds, vFourthSeeds]⟩
    · exact ⟨vR anchor, by simp [seeds, vFourthSeeds]⟩
  · intro i
    cases i
    · apply edgeConnected_pair
      simpa [vU, vV] using cellAt_east anchor 0 1
    · exact edgeConnected_singleton _
  · apply Finset.disjoint_left.mpr
    intro c hc0 hc1
    simp only [seeds, vFourthSeeds, Finset.mem_insert,
      Finset.mem_singleton] at hc0 hc1
    rcases hc0 with rfl | rfl
    <;> simp [vU, vV, vR, cellAt] at hc1 <;> omega
  · simp [seeds, vFourthSeeds]
  · intro d c hd hc hcDeleted hadj
    have hseed := v_lowerDomino_boundary frame hd hc hcDeleted hadj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hseed
    rcases hseed with rfl | rfl | rfl
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor] using
        (show vU anchor ∈ seeds false by simp [seeds, vFourthSeeds])
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor] using
        (show vV anchor ∈ seeds false by simp [seeds, vFourthSeeds])
    · apply mem_coveredCells.mpr
      refine ⟨true, ?_⟩
      simpa only [anchor] using
        (show vR anchor ∈ seeds true by simp [seeds, vFourthSeeds])

def vFifthSystem {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : vS x.2.1 ∈ x.1.toPolyomino.cells) : SeedSystem Bool := by
  let P := x.1.toPolyomino
  let anchor := x.2.1
  let deleted : Finset Cell := {vA anchor, vB anchor}
  let ambient := P.cells \ deleted
  let seeds := vFifthSeeds ambient anchor
  refine deletionSeedSystem P deleted seeds ?_ ?_ ?_ ?_ (vU anchor) ?_ ?_
  · intro i
    cases i
    · apply chainSeed_subset
      · exact Finset.mem_sdiff.mpr ⟨hu, by
          simp [deleted, vA, vU, vB, cellAt]⟩
      · exact Finset.mem_sdiff.mpr ⟨hv, by
          simp [deleted, vV, vA, vB, cellAt]⟩
    · apply chainSeed_subset
      · exact Finset.mem_sdiff.mpr ⟨hr, by
          simp [deleted, vR, vA, vB, cellAt]⟩
      · exact Finset.mem_sdiff.mpr ⟨hs, by
          simp [deleted, vS, vA, vB, cellAt]⟩
  · intro i
    cases i <;> apply chainSeed_nonempty
  · intro i
    cases i
    · apply chainSeed_connected
      · simpa [vU, vV] using cellAt_east anchor 0 1
      · simpa [vV, vTopV] using cellAt_north anchor 1 1
    · apply chainSeed_connected
      · simpa [vR, vS] using cellAt_north anchor 2 0
      · simpa [vS, vTopS] using cellAt_north anchor 2 1
  · apply Finset.disjoint_left.mpr
    intro c hc0 hc1
    have hc0' : c = vU anchor ∨ c = vV anchor ∨
        (c = vTopV anchor ∧ vTopV anchor ∈ ambient) := by
      exact (mem_chainSeed_iff.mp (show
        c ∈ chainSeed ambient (vU anchor) (vV anchor) (vTopV anchor) from hc0))
    have hc1' : c = vR anchor ∨ c = vS anchor ∨
        (c = vTopS anchor ∧ vTopS anchor ∈ ambient) := by
      exact (mem_chainSeed_iff.mp (show
        c ∈ chainSeed ambient (vR anchor) (vS anchor) (vTopS anchor) from hc1))
    rcases hc0' with h0 | h0 | ⟨h0, _⟩ <;>
      rcases hc1' with h1 | h1 | ⟨h1, _⟩ <;>
      have h := h0.symm.trans h1 <;>
      simp [vU, vV, vR, vS, vTopV, vTopS, cellAt] at h
  · simpa only [seeds] using vU_mem_vFifthSeeds ambient anchor
  · intro d c hd hc hcDeleted hadj
    have hseed := v_lowerDomino_boundary frame hd hc hcDeleted hadj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hseed
    rcases hseed with rfl | rfl | rfl
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor, seeds] using vU_mem_vFifthSeeds ambient anchor
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor, seeds] using vV_mem_vFifthSeeds ambient anchor
    · apply mem_coveredCells.mpr
      refine ⟨true, ?_⟩
      simpa only [anchor, seeds] using vR_mem_vFifthSeeds ambient anchor

/-! Stable projections of the seeded systems.  The branch proofs use these
instead of unfolding proof-valued `SeedSystem` constructors. -/

@[simp]
theorem vSecondSystem_cells {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∉ x.1.toPolyomino.cells) :
    (vSecondSystem x frame hu hv).cells =
      x.1.toPolyomino.cells \ {vA x.2.1, vB x.2.1} := by
  rfl

@[simp]
theorem vSecondSystem_seeds {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∉ x.1.toPolyomino.cells) (i : Bool) :
    (vSecondSystem x frame hu hv).seeds i = vSecondSeeds x.2.1 i := by
  rfl

@[simp]
theorem vFourthSystem_cells {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells) :
    (vFourthSystem x frame hu hv hr).cells =
      x.1.toPolyomino.cells \ {vA x.2.1, vB x.2.1} := by
  rfl

@[simp]
theorem vFourthSystem_seeds {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells) (i : Bool) :
    (vFourthSystem x frame hu hv hr).seeds i = vFourthSeeds x.2.1 i := by
  rfl

@[simp]
theorem vFifthSystem_cells {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : vS x.2.1 ∈ x.1.toPolyomino.cells) :
    (vFifthSystem x frame hu hv hr hs).cells =
      x.1.toPolyomino.cells \ {vA x.2.1, vB x.2.1} := by
  rfl

@[simp]
theorem vFifthSystem_seeds {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : vS x.2.1 ∈ x.1.toPolyomino.cells) (i : Bool) :
    (vFifthSystem x frame hu hv hr hs).seeds i =
      vFifthSeeds
        (x.1.toPolyomino.cells \ {vA x.2.1, vB x.2.1}) x.2.1 i := by
  rfl

theorem vFifthSystem_vU_mem {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : vS x.2.1 ∈ x.1.toPolyomino.cells) :
    vU x.2.1 ∈ (vFifthSystem x frame hu hv hr hs).seeds false := by
  rw [vFifthSystem_seeds]
  exact vU_mem_vFifthSeeds _ _

theorem vFifthSystem_vV_mem {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : vS x.2.1 ∈ x.1.toPolyomino.cells) :
    vV x.2.1 ∈ (vFifthSystem x frame hu hv hr hs).seeds false := by
  rw [vFifthSystem_seeds]
  exact vV_mem_vFifthSeeds _ _

theorem vFifthSystem_vR_mem {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : vS x.2.1 ∈ x.1.toPolyomino.cells) :
    vR x.2.1 ∈ (vFifthSystem x frame hu hv hr hs).seeds true := by
  rw [vFifthSystem_seeds]
  exact vR_mem_vFifthSeeds _ _

theorem vFifthSystem_vS_mem {n : ℕ} (x : MarkedOccurrence .v n)
    (frame : VFrame x.1.toPolyomino.cells x.2.1)
    (hu : vU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : vV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : vR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : vS x.2.1 ∈ x.1.toPolyomino.cells) :
    vS x.2.1 ∈ (vFifthSystem x frame hu hv hr hs).seeds true := by
  rw [vFifthSystem_seeds]
  exact vS_mem_vFifthSeeds _ _

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

/-! ## Shared branch-remainder utilities -/

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

end GeometricVInternal
end LeanProofs.KlarnerConstant
