import KlarnerConstant.GeometricQCore

/-!
# Seeded geometry for the five branches of the `Q` recurrence

This module defines the three seeded systems, the one- and two-cell deletion
remainders, and the target-pattern proofs for all five occupancy branches.
Finite encoders and their recovery proofs are isolated in
`GeometricQEndpoint`.
-/

namespace LeanProofs.KlarnerConstant
namespace QProof

/-! ## The three seeded systems used by the convolution branches -/

def qSecondSeeds (anchor : Cell) : Bool → Finset Cell
  | false => {qU anchor}
  | true => {qB anchor}

def qFourthSeeds (anchor : Cell) : Bool → Finset Cell
  | false => {qU anchor, qV anchor}
  | true => {qR anchor}

def qFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    Bool → Finset Cell
  | false => chainSeed cells (qU anchor) (qV anchor) (qTopV anchor)
  | true => chainSeed cells (qR anchor) (qS anchor) (qTopS anchor)

theorem qU_mem_qFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    qU anchor ∈ qFifthSeeds cells anchor false := by
  by_cases h : qTopV anchor ∈ cells <;>
    simp [qFifthSeeds, chainSeed, h]

theorem qV_mem_qFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    qV anchor ∈ qFifthSeeds cells anchor false := by
  by_cases h : qTopV anchor ∈ cells <;>
    simp [qFifthSeeds, chainSeed, h]

theorem qR_mem_qFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    qR anchor ∈ qFifthSeeds cells anchor true := by
  by_cases h : qTopS anchor ∈ cells <;>
    simp [qFifthSeeds, chainSeed, h]

theorem qS_mem_qFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    qS anchor ∈ qFifthSeeds cells anchor true := by
  by_cases h : qTopS anchor ∈ cells <;>
    simp [qFifthSeeds, chainSeed, h]

def qSecondSystem {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells) : SeedSystem Bool := by
  let P := x.1.toPolyomino
  let anchor := x.2.1
  let deleted : Finset Cell := {qA anchor}
  let seeds := qSecondSeeds anchor
  refine deletionSeedSystem P deleted seeds ?_ ?_ ?_ ?_ (qU anchor) ?_ ?_
  · intro i
    cases i
    · intro c hc
      have hc' : c = qU anchor := by simpa [seeds, qSecondSeeds] using hc
      subst c
      exact Finset.mem_sdiff.mpr ⟨hu, by simp [deleted, qA, qU]⟩
    · intro c hc
      have hc' : c = qB anchor := by simpa [seeds, qSecondSeeds] using hc
      subst c
      exact Finset.mem_sdiff.mpr ⟨by simpa [P, anchor, qB] using frame.b_mem,
        by simp [deleted, qA, qB]⟩
  · intro i
    cases i <;> simp [seeds, qSecondSeeds]
  · intro i
    cases i <;> simp only [seeds, qSecondSeeds]
    <;> apply edgeConnected_singleton
  · apply Finset.disjoint_left.mpr
    intro c hc0 hc1
    simp only [seeds, qSecondSeeds, Finset.mem_singleton] at hc0 hc1
    subst c
    exact qU_ne_qB anchor hc1
  · simp [seeds, qSecondSeeds]
  · intro d c hd hc hcDeleted hadj
    have hd' : d = qA anchor := by simpa [deleted] using hd
    subst d
    rcases q_a_neighbors frame hc hadj with rfl | rfl
    · apply mem_coveredCells.mpr
      refine ⟨true, ?_⟩
      simpa only [anchor] using
        (show qB anchor ∈ seeds true by simp [seeds, qSecondSeeds])
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor] using
        (show qU anchor ∈ seeds false by simp [seeds, qSecondSeeds])

@[simp]
theorem qSecondSystem_cells {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells) :
    (qSecondSystem x frame hu).cells =
      x.1.toPolyomino.cells \ {qA x.2.1} := by
  rfl

@[simp]
theorem qSecondSystem_seeds {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells) (i : Bool) :
    (qSecondSystem x frame hu).seeds i = qSecondSeeds x.2.1 i := by
  rfl

def qFourthSystem {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells) : SeedSystem Bool := by
  let P := x.1.toPolyomino
  let anchor := x.2.1
  let deleted : Finset Cell := {qA anchor, qB anchor}
  let seeds := qFourthSeeds anchor
  refine deletionSeedSystem P deleted seeds ?_ ?_ ?_ ?_ (qU anchor) ?_ ?_
  · intro i
    cases i
    · intro c hc
      simp only [seeds, qFourthSeeds, Finset.mem_insert,
        Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact Finset.mem_sdiff.mpr ⟨hu, by
          simp [deleted, qA, qU, qB]⟩
      · exact Finset.mem_sdiff.mpr ⟨hv, by
          simp [deleted, qV, qA, qB, cellAt]⟩
    · intro c hc
      have hc' : c = qR anchor := by simpa [seeds, qFourthSeeds] using hc
      subst c
      exact Finset.mem_sdiff.mpr ⟨hr, by
        simp [deleted, qR, qA, qB, cellAt]⟩
  · intro i
    cases i
    · exact ⟨qU anchor, by simp [seeds, qFourthSeeds]⟩
    · exact ⟨qR anchor, by simp [seeds, qFourthSeeds]⟩
  · intro i
    cases i
    · apply edgeConnected_pair
      simpa [qU, qV] using cellAt_east anchor 0 1
    · exact edgeConnected_singleton _
  · apply Finset.disjoint_left.mpr
    intro c hc0 hc1
    simp only [seeds, qFourthSeeds, Finset.mem_insert,
      Finset.mem_singleton] at hc0 hc1
    rcases hc0 with rfl | rfl
    <;> simp [qU, qV, qR, cellAt] at hc1
  · simp [seeds, qFourthSeeds]
  · intro d c hd hc hcDeleted hadj
    have hseed := q_lowerDomino_boundary frame hd hc hcDeleted hadj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hseed
    rcases hseed with rfl | rfl | rfl
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor] using
        (show qU anchor ∈ seeds false by simp [seeds, qFourthSeeds])
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor] using
        (show qV anchor ∈ seeds false by simp [seeds, qFourthSeeds])
    · apply mem_coveredCells.mpr
      refine ⟨true, ?_⟩
      simpa only [anchor] using
        (show qR anchor ∈ seeds true by simp [seeds, qFourthSeeds])

@[simp]
theorem qFourthSystem_cells {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells) :
    (qFourthSystem x frame hu hv hr).cells =
      x.1.toPolyomino.cells \ {qA x.2.1, qB x.2.1} := by
  rfl

@[simp]
theorem qFourthSystem_seeds {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells) (i : Bool) :
    (qFourthSystem x frame hu hv hr).seeds i = qFourthSeeds x.2.1 i := by
  rfl

def qFifthSystem {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : qS x.2.1 ∈ x.1.toPolyomino.cells) : SeedSystem Bool := by
  let P := x.1.toPolyomino
  let anchor := x.2.1
  let deleted : Finset Cell := {qA anchor, qB anchor}
  let ambient := P.cells \ deleted
  let seeds := qFifthSeeds ambient anchor
  refine deletionSeedSystem P deleted seeds ?_ ?_ ?_ ?_ (qU anchor) ?_ ?_
  · intro i
    cases i
    · apply chainSeed_subset
      · exact Finset.mem_sdiff.mpr ⟨hu, by
          simp [deleted, qA, qU, qB]⟩
      · exact Finset.mem_sdiff.mpr ⟨hv, by
          simp [deleted, qV, qA, qB, cellAt]⟩
    · apply chainSeed_subset
      · exact Finset.mem_sdiff.mpr ⟨hr, by
          simp [deleted, qR, qA, qB, cellAt]⟩
      · exact Finset.mem_sdiff.mpr ⟨hs, by
          simp [deleted, qS, qA, qB, cellAt]⟩
  · intro i
    cases i <;> apply chainSeed_nonempty
  · intro i
    cases i
    · apply chainSeed_connected
      · simpa [qU, qV] using cellAt_east anchor 0 1
      · simpa [qV, qTopV] using cellAt_north anchor 1 1
    · apply chainSeed_connected
      · simpa [qR, qS] using cellAt_north anchor 2 0
      · simpa [qS, qTopS] using cellAt_north anchor 2 1
  · apply Finset.disjoint_left.mpr
    intro c hc0 hc1
    have hc0' : c = qU anchor ∨ c = qV anchor ∨
        (c = qTopV anchor ∧ qTopV anchor ∈ ambient) := by
      exact (mem_chainSeed_iff.mp (show
        c ∈ chainSeed ambient (qU anchor) (qV anchor) (qTopV anchor) from hc0))
    have hc1' : c = qR anchor ∨ c = qS anchor ∨
        (c = qTopS anchor ∧ qTopS anchor ∈ ambient) := by
      exact (mem_chainSeed_iff.mp (show
        c ∈ chainSeed ambient (qR anchor) (qS anchor) (qTopS anchor) from hc1))
    rcases hc0' with h0 | h0 | ⟨h0, _⟩ <;>
      rcases hc1' with h1 | h1 | ⟨h1, _⟩ <;>
      have h := h0.symm.trans h1 <;>
      simp [qU, qV, qR, qS, qTopV, qTopS, cellAt] at h
  · simpa only [seeds] using qU_mem_qFifthSeeds ambient anchor
  · intro d c hd hc hcDeleted hadj
    have hseed := q_lowerDomino_boundary frame hd hc hcDeleted hadj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hseed
    rcases hseed with rfl | rfl | rfl
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor, seeds] using qU_mem_qFifthSeeds ambient anchor
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor, seeds] using qV_mem_qFifthSeeds ambient anchor
    · apply mem_coveredCells.mpr
      refine ⟨true, ?_⟩
      simpa only [anchor, seeds] using qR_mem_qFifthSeeds ambient anchor

@[simp]
theorem qFifthSystem_cells {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : qS x.2.1 ∈ x.1.toPolyomino.cells) :
    (qFifthSystem x frame hu hv hr hs).cells =
      x.1.toPolyomino.cells \ {qA x.2.1, qB x.2.1} := by
  rfl

@[simp]
theorem qFifthSystem_seeds {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : qS x.2.1 ∈ x.1.toPolyomino.cells) (i : Bool) :
    (qFifthSystem x frame hu hv hr hs).seeds i =
      qFifthSeeds
        (x.1.toPolyomino.cells \ {qA x.2.1, qB x.2.1}) x.2.1 i := by
  rfl

theorem qFifthSystem_qU_mem {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : qS x.2.1 ∈ x.1.toPolyomino.cells) :
    qU x.2.1 ∈ (qFifthSystem x frame hu hv hr hs).seeds false := by
  rw [qFifthSystem_seeds]
  exact qU_mem_qFifthSeeds _ _

theorem qFifthSystem_qV_mem {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : qS x.2.1 ∈ x.1.toPolyomino.cells) :
    qV x.2.1 ∈ (qFifthSystem x frame hu hv hr hs).seeds false := by
  rw [qFifthSystem_seeds]
  exact qV_mem_qFifthSeeds _ _

theorem qFifthSystem_qR_mem {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : qS x.2.1 ∈ x.1.toPolyomino.cells) :
    qR x.2.1 ∈ (qFifthSystem x frame hu hv hr hs).seeds true := by
  rw [qFifthSystem_seeds]
  exact qR_mem_qFifthSeeds _ _

theorem qFifthSystem_qS_mem {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : qS x.2.1 ∈ x.1.toPolyomino.cells) :
    qS x.2.1 ∈ (qFifthSystem x frame hu hv hr hs).seeds true := by
  rw [qFifthSystem_seeds]
  exact qS_mem_qFifthSeeds _ _

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

def qFirstRemainder {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∉ x.1.toPolyomino.cells) : Polyomino :=
  eraseLeafPolyomino x.1.toPolyomino (qA x.2.1) (qB x.2.1)
    (by simpa [qA] using frame.a_mem)
    (by simpa [qB] using frame.b_mem)
    (qA_ne_qB x.2.1)
    (by
      intro c hc hadj
      rcases q_a_neighbors frame hc hadj with h | h
      · exact h
      · exact (hu (h ▸ hc)).elim)

theorem qFirst_g_occursAt {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∉ x.1.toPolyomino.cells) :
    buiGPattern.OccursAt
      (diagonalSymmetry.transformPolyomino (qFirstRemainder x frame hu)).cells
      (diagonalSymmetry.equiv (qB x.2.1)) := by
  constructor
  · intro offset hoff
    have hoff' : offset = (0, 0) := by simpa [buiGPattern] using hoff
    subst offset
    rw [show diagonalSymmetry.equiv (qB x.2.1) + (0, 0) =
        diagonalSymmetry.equiv (qB x.2.1) by simp]
    apply transform_mem
    exact Finset.mem_erase.mpr ⟨(qA_ne_qB x.2.1).symm,
      by simpa [qB] using frame.b_mem⟩
  · intro offset hoff
    simp only [buiGPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h <;> subst offset
    · rw [show diagonalSymmetry.equiv (qB x.2.1) + (-1, 0) =
          diagonalSymmetry.equiv (cellAt x.2.1 1 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, qB, cellAt] <;> omega]
      apply transform_not_mem
      exact fun hm => frame.southeast_not_mem (Finset.mem_erase.mp hm).2
    · rw [show diagonalSymmetry.equiv (qB x.2.1) + (-1, -1) =
          diagonalSymmetry.equiv (cellAt x.2.1 0 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, qB, cellAt] <;> omega]
      apply transform_not_mem
      exact fun hm => frame.south_not_mem (Finset.mem_erase.mp hm).2
    · rw [show diagonalSymmetry.equiv (qB x.2.1) + (0, -1) =
          diagonalSymmetry.equiv (qA x.2.1) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, qA, qB, cellAt] <;> omega]
      apply transform_not_mem
      exact fun hm => (Finset.mem_erase.mp hm).1 rfl
    · rw [show diagonalSymmetry.equiv (qB x.2.1) + (1, -1) =
          diagonalSymmetry.equiv (qU x.2.1) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, qB, qU, cellAt] <;> omega]
      apply transform_not_mem
      exact fun hm => hu (Finset.mem_erase.mp hm).2

theorem qSecond_left_g_occursAt {n : ℕ}
    (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∉ x.1.toPolyomino.cells)
    (part : SeededPartition (qSecondSystem x frame hu)) :
    buiGPattern.OccursAt
      (verticalSymmetry.transformPolyomino (part.territoryPolyomino false)).cells
      (verticalSymmetry.equiv (qU x.2.1)) := by
  constructor
  · intro offset hoff
    have : offset = (0, 0) := by simpa [buiGPattern] using hoff
    subst offset
    rw [show ((0, 0) : Cell) = 0 by rfl, add_zero]
    exact transform_mem verticalSymmetry (part.territoryPolyomino false)
      (part.seed_subset false (show qU x.2.1 ∈
          (qSecondSystem x frame hu).seeds false from by
        rw [qSecondSystem_seeds]
        simp [qSecondSeeds]))
  · intro offset hoff
    simp only [buiGPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h <;> subst offset
    · rw [show verticalSymmetry.equiv (qU x.2.1) + (-1, 0) =
          verticalSymmetry.equiv (qV x.2.1) by
          apply Prod.ext <;>
            dsimp [verticalSymmetry, verticalEquiv, qU, qV, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [qSecondSystem_cells]
      intro hm
      exact hv (Finset.mem_sdiff.mp hm).1
    · rw [show verticalSymmetry.equiv (qU x.2.1) + (-1, -1) =
          verticalSymmetry.equiv (qB x.2.1) by
          apply Prod.ext <;>
            dsimp [verticalSymmetry, verticalEquiv, qU, qB, cellAt] <;> omega]
      apply transform_not_mem
      exact territory_not_mem_of_other_seed part false true (by decide)
        (by rw [qSecondSystem_seeds]; simp [qSecondSeeds])
    · rw [show verticalSymmetry.equiv (qU x.2.1) + (0, -1) =
          verticalSymmetry.equiv (qA x.2.1) by
          apply Prod.ext <;>
            dsimp [verticalSymmetry, verticalEquiv, qU, qA, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [qSecondSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    · rw [show verticalSymmetry.equiv (qU x.2.1) + (1, -1) =
          verticalSymmetry.equiv (cellAt x.2.1 (-1) 0) by
          apply Prod.ext <;>
            dsimp [verticalSymmetry, verticalEquiv, qU, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [qSecondSystem_cells]
      intro hm
      exact frame.left_not_mem (Finset.mem_sdiff.mp hm).1

theorem qSecond_right_e_occursAt {n : ℕ}
    (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∉ x.1.toPolyomino.cells)
    (part : SeededPartition (qSecondSystem x frame hu)) :
    buiEPattern.OccursAt
      (diagonalSymmetry.transformPolyomino (part.territoryPolyomino true)).cells
      (diagonalSymmetry.equiv (qB x.2.1)) := by
  constructor
  · intro offset hoff
    have : offset = (0, 0) := by simpa [buiEPattern] using hoff
    subst offset
    rw [show ((0, 0) : Cell) = 0 by rfl, add_zero]
    exact transform_mem diagonalSymmetry (part.territoryPolyomino true)
      (part.seed_subset true (show qB x.2.1 ∈
          (qSecondSystem x frame hu).seeds true from by
        rw [qSecondSystem_seeds]
        simp [qSecondSeeds]))
  · intro offset hoff
    simp only [buiEPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h | h <;> subst offset
    · rw [show diagonalSymmetry.equiv (qB x.2.1) + (-1, 0) =
          diagonalSymmetry.equiv (cellAt x.2.1 1 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, qB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [qSecondSystem_cells]
      intro hm
      exact frame.southeast_not_mem (Finset.mem_sdiff.mp hm).1
    · rw [show diagonalSymmetry.equiv (qB x.2.1) + (1, 0) =
          diagonalSymmetry.equiv (qV x.2.1) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, qB, qV, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [qSecondSystem_cells]
      intro hm
      exact hv (Finset.mem_sdiff.mp hm).1
    · rw [show diagonalSymmetry.equiv (qB x.2.1) + (-1, -1) =
          diagonalSymmetry.equiv (cellAt x.2.1 0 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, qB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [qSecondSystem_cells]
      intro hm
      exact frame.south_not_mem (Finset.mem_sdiff.mp hm).1
    · rw [show diagonalSymmetry.equiv (qB x.2.1) + (0, -1) =
          diagonalSymmetry.equiv (qA x.2.1) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, qA, qB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [qSecondSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    · rw [show diagonalSymmetry.equiv (qB x.2.1) + (1, -1) =
          diagonalSymmetry.equiv (qU x.2.1) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, qB, qU, cellAt] <;> omega]
      apply transform_not_mem
      exact territory_not_mem_of_other_seed part true false (by decide)
        (by rw [qSecondSystem_seeds]; simp [qSecondSeeds])

def qThirdRemainder {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∉ x.1.toPolyomino.cells) : Polyomino :=
  eraseLowerDominoPolyomino x.1.toPolyomino
    (qA x.2.1) (qB x.2.1) (qU x.2.1) (qV x.2.1)
    (by simpa [qA] using frame.a_mem) (by simpa [qB] using frame.b_mem)
    hu hv (qA_ne_qB _) (qA_ne_qU _) (qU_ne_qB _)
    ((qA_ne_qV _).symm) (qB_ne_qV _)
    (by simpa [qU, qV] using cellAt_east x.2.1 0 1)
    (q_a_neighbors frame) (q_b_neighbors_of_r_absent frame hr)

theorem qThird_u_mem {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∉ x.1.toPolyomino.cells) :
    qU x.2.1 ∈ (qThirdRemainder x frame hu hv hr).cells := by
  exact Finset.mem_erase.mpr ⟨qU_ne_qB x.2.1,
    Finset.mem_erase.mpr ⟨(qA_ne_qU x.2.1).symm, hu⟩⟩

theorem qThird_u_occursAt {n : ℕ} (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∉ x.1.toPolyomino.cells) :
    buiUPattern.OccursAt (qThirdRemainder x frame hu hv hr).cells (qU x.2.1) := by
  constructor
  · intro offset hoffset
    simp only [buiUPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with rfl | rfl
    · rw [qU_add_offset]
      norm_num
      exact qThird_u_mem x frame hu hv hr
    · rw [qU_add_offset]
      norm_num
      change qV x.2.1 ∈ _
      exact Finset.mem_erase.mpr ⟨(qB_ne_qV x.2.1).symm,
        Finset.mem_erase.mpr ⟨(qA_ne_qV x.2.1).symm, hv⟩⟩
  · intro offset hoffset
    simp only [buiUPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with h | h | h | h <;> subst offset
    · rw [qU_add_offset]
      norm_num
      intro hm
      exact frame.left_not_mem
        (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).2
    · rw [qU_add_offset]
      norm_num
      change qA x.2.1 ∉ _
      intro hm
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1 rfl
    · rw [qU_add_offset]
      norm_num
      change qB x.2.1 ∉ _
      intro hm
      exact (Finset.mem_erase.mp hm).1 rfl
    · rw [qU_add_offset]
      norm_num
      change qR x.2.1 ∉ _
      intro hm
      exact hr (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).2

theorem qFourth_left_t_occursAt {n : ℕ}
    (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : qS x.2.1 ∉ x.1.toPolyomino.cells)
    (part : SeededPartition (qFourthSystem x frame hu hv hr)) :
    buiTPattern.OccursAt
      (verticalSymmetry.transformPolyomino (part.territoryPolyomino false)).cells
      (verticalSymmetry.equiv (qV x.2.1)) := by
  constructor
  · intro offset hoffset
    simp only [buiTPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with rfl | rfl
    · rw [show ((0, 0) : Cell) = 0 by rfl, add_zero]
      exact transform_mem verticalSymmetry (part.territoryPolyomino false)
        (part.seed_subset false (show qV x.2.1 ∈
            (qFourthSystem x frame hu hv hr).seeds false from by
          rw [qFourthSystem_seeds]
          simp [qFourthSeeds]))
    · rw [show verticalSymmetry.equiv (qV x.2.1) + (1, 0) =
          verticalSymmetry.equiv (qU x.2.1) by
          apply Prod.ext <;>
            dsimp [verticalSymmetry, verticalEquiv, qV, qU, cellAt] <;> omega]
      exact transform_mem verticalSymmetry (part.territoryPolyomino false)
        (part.seed_subset false (show qU x.2.1 ∈
            (qFourthSystem x frame hu hv hr).seeds false from by
          rw [qFourthSystem_seeds]
          simp [qFourthSeeds]))
  · intro offset hoffset
    simp only [buiTPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with h | h | h | h | h <;> subst offset
    · rw [show verticalSymmetry.equiv (qV x.2.1) + (-1, 0) =
          verticalSymmetry.equiv (qS x.2.1) by
          apply Prod.ext <;>
            dsimp [verticalSymmetry, verticalEquiv, qV, qS, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [qFourthSystem_cells]
      intro hm
      exact hs (Finset.mem_sdiff.mp hm).1
    · rw [show verticalSymmetry.equiv (qV x.2.1) + (-1, -1) =
          verticalSymmetry.equiv (qR x.2.1) by
          apply Prod.ext <;>
            dsimp [verticalSymmetry, verticalEquiv, qV, qR, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_other_seed part false true (by decide)
          (by rw [qFourthSystem_seeds]; simp [qFourthSeeds]))
    · rw [show verticalSymmetry.equiv (qV x.2.1) + (0, -1) =
          verticalSymmetry.equiv (qB x.2.1) by
          apply Prod.ext <;>
            dsimp [verticalSymmetry, verticalEquiv, qV, qB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [qFourthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    · rw [show verticalSymmetry.equiv (qV x.2.1) + (1, -1) =
          verticalSymmetry.equiv (qA x.2.1) by
          apply Prod.ext <;>
            dsimp [verticalSymmetry, verticalEquiv, qV, qA, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [qFourthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    · rw [show verticalSymmetry.equiv (qV x.2.1) + (2, -1) =
          verticalSymmetry.equiv (cellAt x.2.1 (-1) 0) by
          apply Prod.ext <;>
            dsimp [verticalSymmetry, verticalEquiv, qV, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [qFourthSystem_cells]
      intro hm
      exact frame.left_not_mem (Finset.mem_sdiff.mp hm).1

theorem qFourth_right_g_occursAt {n : ℕ}
    (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : qS x.2.1 ∉ x.1.toPolyomino.cells)
    (part : SeededPartition (qFourthSystem x frame hu hv hr)) :
    buiGPattern.OccursAt
      (quarterTurnSymmetry.transformPolyomino (part.territoryPolyomino true)).cells
      (quarterTurnSymmetry.equiv (qR x.2.1)) := by
  constructor
  · intro offset hoff
    have : offset = (0, 0) := by simpa [buiGPattern] using hoff
    subst offset
    rw [show ((0, 0) : Cell) = 0 by rfl, add_zero]
    exact transform_mem quarterTurnSymmetry (part.territoryPolyomino true)
      (part.seed_subset true (show qR x.2.1 ∈
          (qFourthSystem x frame hu hv hr).seeds true from by
        rw [qFourthSystem_seeds]
        simp [qFourthSeeds]))
  · intro offset hoff
    simp only [buiGPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h <;> subst offset
    · rw [show quarterTurnSymmetry.equiv (qR x.2.1) + (-1, 0) =
          quarterTurnSymmetry.equiv (qS x.2.1) by
          apply Prod.ext <;> dsimp [quarterTurnSymmetry, quarterTurnEquiv, qR, qS, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [qFourthSystem_cells]
      intro hm
      exact hs (Finset.mem_sdiff.mp hm).1
    · rw [show quarterTurnSymmetry.equiv (qR x.2.1) + (-1, -1) =
          quarterTurnSymmetry.equiv (qV x.2.1) by
          apply Prod.ext <;> dsimp [quarterTurnSymmetry, quarterTurnEquiv, qR, qV, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_other_seed part true false (by decide)
          (by rw [qFourthSystem_seeds]; simp [qFourthSeeds]))
    · rw [show quarterTurnSymmetry.equiv (qR x.2.1) + (0, -1) =
          quarterTurnSymmetry.equiv (qB x.2.1) by
          apply Prod.ext <;> dsimp [quarterTurnSymmetry, quarterTurnEquiv, qR, qB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [qFourthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    · rw [show quarterTurnSymmetry.equiv (qR x.2.1) + (1, -1) =
          quarterTurnSymmetry.equiv (cellAt x.2.1 1 (-1)) by
          apply Prod.ext <;> dsimp [quarterTurnSymmetry, quarterTurnEquiv, qR, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [qFourthSystem_cells]
      intro hm
      exact frame.southeast_not_mem (Finset.mem_sdiff.mp hm).1

theorem fifth_topS_not_left {n : ℕ}
    (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : qS x.2.1 ∈ x.1.toPolyomino.cells)
    (part : SeededPartition (qFifthSystem x frame hu hv hr hs)) :
    qTopS x.2.1 ∉ part.territories false := by
  by_cases ht : qTopS x.2.1 ∈ (qFifthSystem x frame hu hv hr hs).cells
  · apply territory_not_mem_of_other_seed part false true (by decide)
    rw [qFifthSystem_cells] at ht
    rw [qFifthSystem_seeds]
    simp [qFifthSeeds, chainSeed, ht]
  · exact territory_not_mem_of_not_ambient part false ht

theorem fifth_topV_not_right {n : ℕ}
    (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : qS x.2.1 ∈ x.1.toPolyomino.cells)
    (part : SeededPartition (qFifthSystem x frame hu hv hr hs)) :
    qTopV x.2.1 ∉ part.territories true := by
  by_cases ht : qTopV x.2.1 ∈ (qFifthSystem x frame hu hv hr hs).cells
  · apply territory_not_mem_of_other_seed part true false (by decide)
    rw [qFifthSystem_cells] at ht
    rw [qFifthSystem_seeds]
    simp [qFifthSeeds, chainSeed, ht]
  · exact territory_not_mem_of_not_ambient part true ht

theorem qFifth_left_r_occursAt {n : ℕ}
    (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : qS x.2.1 ∈ x.1.toPolyomino.cells)
    (part : SeededPartition (qFifthSystem x frame hu hv hr hs)) :
    buiRPattern.OccursAt
      (verticalSymmetry.transformPolyomino (part.territoryPolyomino false)).cells
      (verticalSymmetry.equiv (qV x.2.1)) := by
  constructor
  · intro offset hoff
    simp only [buiRPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with rfl | rfl
    · rw [show ((0, 0) : Cell) = 0 by rfl, add_zero]
      exact transform_mem verticalSymmetry (part.territoryPolyomino false)
        (part.seed_subset false
          (qFifthSystem_qV_mem x frame hu hv hr hs))
    · rw [show verticalSymmetry.equiv (qV x.2.1) + (1, 0) =
          verticalSymmetry.equiv (qU x.2.1) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, qV, qU, cellAt] <;> omega]
      exact transform_mem verticalSymmetry (part.territoryPolyomino false)
        (part.seed_subset false
          (qFifthSystem_qU_mem x frame hu hv hr hs))
  · intro offset hoff
    simp only [buiRPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h | h | h <;> subst offset
    · rw [show verticalSymmetry.equiv (qV x.2.1) + (-1, 1) =
          verticalSymmetry.equiv (qTopS x.2.1) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, qV, qTopS, cellAt] <;> omega]
      exact transform_not_mem _ _ (fifth_topS_not_left x frame hu hv hr hs part)
    · rw [show verticalSymmetry.equiv (qV x.2.1) + (-1, 0) =
          verticalSymmetry.equiv (qS x.2.1) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, qV, qS, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_other_seed part false true (by decide)
          (qFifthSystem_qS_mem x frame hu hv hr hs))
    · rw [show verticalSymmetry.equiv (qV x.2.1) + (-1, -1) =
          verticalSymmetry.equiv (qR x.2.1) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, qV, qR, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_other_seed part false true (by decide)
          (qFifthSystem_qR_mem x frame hu hv hr hs))
    · rw [show verticalSymmetry.equiv (qV x.2.1) + (0, -1) =
          verticalSymmetry.equiv (qB x.2.1) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, qV, qB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [qFifthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    · rw [show verticalSymmetry.equiv (qV x.2.1) + (1, -1) =
          verticalSymmetry.equiv (qA x.2.1) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, qV, qA, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [qFifthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    · rw [show verticalSymmetry.equiv (qV x.2.1) + (2, -1) =
          verticalSymmetry.equiv (cellAt x.2.1 (-1) 0) by
          apply Prod.ext <;> dsimp [verticalSymmetry, verticalEquiv, qV, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part false
      rw [qFifthSystem_cells]
      intro hm
      exact frame.left_not_mem (Finset.mem_sdiff.mp hm).1

theorem qFifth_right_u_occursAt {n : ℕ}
    (x : MarkedOccurrence .q n)
    (frame : QFrame x.1.toPolyomino.cells x.2.1)
    (hu : qU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : qV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : qR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : qS x.2.1 ∈ x.1.toPolyomino.cells)
    (part : SeededPartition (qFifthSystem x frame hu hv hr hs)) :
    buiUPattern.OccursAt
      (diagonalSymmetry.transformPolyomino (part.territoryPolyomino true)).cells
      (diagonalSymmetry.equiv (qR x.2.1)) := by
  constructor
  · intro offset hoff
    simp only [buiUPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with rfl | rfl
    · rw [show ((0, 0) : Cell) = 0 by rfl, add_zero]
      exact transform_mem diagonalSymmetry (part.territoryPolyomino true)
        (part.seed_subset true
          (qFifthSystem_qR_mem x frame hu hv hr hs))
    · rw [show diagonalSymmetry.equiv (qR x.2.1) + (1, 0) =
          diagonalSymmetry.equiv (qS x.2.1) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, qR, qS, cellAt] <;> omega]
      exact transform_mem diagonalSymmetry (part.territoryPolyomino true)
        (part.seed_subset true
          (qFifthSystem_qS_mem x frame hu hv hr hs))
  · intro offset hoff
    simp only [buiUPattern, Finset.mem_insert, Finset.mem_singleton] at hoff
    rcases hoff with h | h | h | h <;> subst offset
    · rw [show diagonalSymmetry.equiv (qR x.2.1) + (-1, -1) =
          diagonalSymmetry.equiv (cellAt x.2.1 1 (-1)) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, qR, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [qFifthSystem_cells]
      intro hm
      exact frame.southeast_not_mem (Finset.mem_sdiff.mp hm).1
    · rw [show diagonalSymmetry.equiv (qR x.2.1) + (0, -1) =
          diagonalSymmetry.equiv (qB x.2.1) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, qR, qB, cellAt] <;> omega]
      apply transform_not_mem
      apply territory_not_mem_of_not_ambient part true
      rw [qFifthSystem_cells]
      exact fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    · rw [show diagonalSymmetry.equiv (qR x.2.1) + (1, -1) =
          diagonalSymmetry.equiv (qV x.2.1) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, qR, qV, cellAt] <;> omega]
      exact transform_not_mem _ _
        (territory_not_mem_of_other_seed part true false (by decide)
          (qFifthSystem_qV_mem x frame hu hv hr hs))
    · rw [show diagonalSymmetry.equiv (qR x.2.1) + (2, -1) =
          diagonalSymmetry.equiv (qTopV x.2.1) by
          apply Prod.ext <;> dsimp [diagonalSymmetry, diagonalEquiv, qR, qTopV, cellAt] <;> omega]
      exact transform_not_mem _ _ (fifth_topV_not_right x frame hu hv hr hs part)

end QProof
end LeanProofs.KlarnerConstant
