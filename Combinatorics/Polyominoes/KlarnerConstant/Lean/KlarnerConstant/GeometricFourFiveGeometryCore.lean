import KlarnerConstant.GeometricFourFiveCore

/-!
# Foundational geometry for the five-branch `S` recurrence

This module builds the local frame, elementary grid lemmas, seeded
decompositions, and connectivity-preserving deletion retractions used by the
target-pattern geometry.
-/

namespace LeanProofs.KlarnerConstant

namespace GeometricFourFiveInternal

/-! ## The marked `S` frame and elementary grid facts -/

structure SFrame (cells : Finset Cell) (anchor : Cell) : Prop where
  a_mem : cellAt anchor 0 0 ∈ cells
  b_mem : cellAt anchor 1 0 ∈ cells
  leftNorth_not_mem : cellAt anchor (-1) 1 ∉ cells
  left_not_mem : cellAt anchor (-1) 0 ∉ cells
  southwest_not_mem : cellAt anchor (-1) (-1) ∉ cells
  south_not_mem : cellAt anchor 0 (-1) ∉ cells
  southeast_not_mem : cellAt anchor 1 (-1) ∉ cells

def sA (anchor : Cell) := cellAt anchor 0 0
def sB (anchor : Cell) := cellAt anchor 1 0
def sU (anchor : Cell) := cellAt anchor 0 1
def sV (anchor : Cell) := cellAt anchor 1 1
def sR (anchor : Cell) := cellAt anchor 2 0
def sS (anchor : Cell) := cellAt anchor 2 1
def sTopV (anchor : Cell) := cellAt anchor 1 2
def sTopS (anchor : Cell) := cellAt anchor 2 2

@[simp]
theorem sA_add_offset (anchor : Cell) (dx dy : ℤ) :
    sA anchor + (dx, dy) = cellAt anchor dx dy := by
  simp [sA]

@[simp]
theorem sB_add_offset (anchor : Cell) (dx dy : ℤ) :
    sB anchor + (dx, dy) = cellAt anchor (1 + dx) dy := by
  simp [sB]

@[simp]
theorem sU_add_offset (anchor : Cell) (dx dy : ℤ) :
    sU anchor + (dx, dy) = cellAt anchor dx (1 + dy) := by
  simp [sU]

@[simp]
theorem sV_add_offset (anchor : Cell) (dx dy : ℤ) :
    sV anchor + (dx, dy) = cellAt anchor (1 + dx) (1 + dy) := by
  simp [sV]

@[simp]
theorem sR_add_offset (anchor : Cell) (dx dy : ℤ) :
    sR anchor + (dx, dy) = cellAt anchor (2 + dx) dy := by
  simp [sR]

@[simp]
theorem sS_add_offset (anchor : Cell) (dx dy : ℤ) :
    sS anchor + (dx, dy) = cellAt anchor (2 + dx) (1 + dy) := by
  simp [sS]

theorem sFrame_of_occursAt {cells : Finset Cell} {anchor : Cell}
    (h : buiSPattern.OccursAt cells anchor) : SFrame cells anchor := by
  constructor
  · exact h.1 (0, 0) (by simp [buiSPattern])
  · exact h.1 (1, 0) (by simp [buiSPattern])
  · exact h.2 (-1, 1) (by simp [buiSPattern])
  · exact h.2 (-1, 0) (by simp [buiSPattern])
  · exact h.2 (-1, -1) (by simp [buiSPattern])
  · exact h.2 (0, -1) (by simp [buiSPattern])
  · exact h.2 (1, -1) (by simp [buiSPattern])

theorem marked_occursAt {kind : BuiNeighborhood} {n : ℕ}
    (x : MarkedOccurrence kind n) :
    kind.pattern.OccursAt x.1.toPolyomino.cells x.2.1 := by
  exact ((mem_occurrenceAnchors_iff _ _ _).1 x.2.2).2

theorem sA_ne_sB (anchor : Cell) : sA anchor ≠ sB anchor := by
  intro h
  have := congrArg Prod.fst h
  simp [sA, sB, cellAt] at this

theorem sA_ne_sU (anchor : Cell) : sA anchor ≠ sU anchor := by
  intro h
  have := congrArg Prod.snd h
  simp [sA, sU, cellAt] at this

theorem sB_ne_sV (anchor : Cell) : sB anchor ≠ sV anchor := by
  intro h
  have := congrArg Prod.snd h
  simp [sB, sV, cellAt] at this

theorem sA_ne_sV (anchor : Cell) : sA anchor ≠ sV anchor := by
  intro h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp [sA, sV, cellAt] at hx hy

theorem sU_ne_sB (anchor : Cell) : sU anchor ≠ sB anchor := by
  intro h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp [sU, sB, cellAt] at hx hy

theorem s_a_neighbors {cells : Finset Cell} {anchor c : Cell}
    (frame : SFrame cells anchor) (hc : c ∈ cells)
    (hadj : EdgeAdjacent (sA anchor) c) :
    c = sB anchor ∨ c = sU anchor := by
  rw [sA, cellAt_zero] at hadj
  rcases hadj with h | h | h | h
  · left
    calc
      c = (anchor.1 + 1, anchor.2) := h
      _ = sB anchor := by apply Prod.ext <;> dsimp [sB, cellAt] <;> omega
  · exfalso
    apply frame.left_not_mem
    have hc' : c = cellAt anchor (-1) 0 := by
      calc
        c = (anchor.1 - 1, anchor.2) := h
        _ = cellAt anchor (-1) 0 := by
          apply Prod.ext <;> dsimp [cellAt] <;> omega
    simpa [hc'] using hc
  · right
    calc
      c = (anchor.1, anchor.2 + 1) := h
      _ = sU anchor := by apply Prod.ext <;> dsimp [sU, cellAt] <;> omega
  · exfalso
    apply frame.south_not_mem
    have hc' : c = cellAt anchor 0 (-1) := by
      calc
        c = (anchor.1, anchor.2 - 1) := h
        _ = cellAt anchor 0 (-1) := by
          apply Prod.ext <;> dsimp [cellAt] <;> omega
    simpa [hc'] using hc

theorem s_b_neighbors_of_r_absent
    {cells : Finset Cell} {anchor c : Cell}
    (frame : SFrame cells anchor) (hr : sR anchor ∉ cells)
    (hc : c ∈ cells) (hadj : EdgeAdjacent (sB anchor) c) :
    c = sA anchor ∨ c = sV anchor := by
  rcases hadj with h | h | h | h
  · exfalso
    apply hr
    have hc' : c = sR anchor := by
      calc
        c = ((sB anchor).1 + 1, (sB anchor).2) := h
        _ = sR anchor := by
          apply Prod.ext <;> dsimp [sB, sR, cellAt] <;> omega
    simpa [hc'] using hc
  · left
    calc
      c = ((sB anchor).1 - 1, (sB anchor).2) := h
      _ = sA anchor := by
        apply Prod.ext <;> dsimp [sA, sB, cellAt] <;> omega
  · right
    calc
      c = ((sB anchor).1, (sB anchor).2 + 1) := h
      _ = sV anchor := by
        apply Prod.ext <;> dsimp [sV, sB, cellAt] <;> omega
  · exfalso
    apply frame.southeast_not_mem
    have hc' : c = cellAt anchor 1 (-1) := by
      calc
        c = ((sB anchor).1, (sB anchor).2 - 1) := h
        _ = cellAt anchor 1 (-1) := by
          apply Prod.ext <;> dsimp [sB, cellAt] <;> omega
    simpa [hc'] using hc

theorem s_lowerDomino_boundary {cells : Finset Cell}
    {anchor d c : Cell} (frame : SFrame cells anchor)
    (hd : d ∈ ({sA anchor, sB anchor} : Finset Cell))
    (hc : c ∈ cells) (hcDeleted : c ∉ ({sA anchor, sB anchor} : Finset Cell))
    (hadj : EdgeAdjacent d c) :
    c ∈ ({sU anchor, sV anchor, sR anchor} : Finset Cell) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl
  · rcases s_a_neighbors frame hc hadj with rfl | rfl
    · exact (hcDeleted (by simp)).elim
    · simp
  · rcases hadj with h | h | h | h
    · have hc' : c = sR anchor := by
        calc
          c = ((sB anchor).1 + 1, (sB anchor).2) := h
          _ = sR anchor := by
            apply Prod.ext <;> dsimp [sB, sR, cellAt] <;> omega
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr hc')
    · have hca : c = sA anchor := by
        calc
          c = ((sB anchor).1 - 1, (sB anchor).2) := h
          _ = sA anchor := by
            apply Prod.ext <;> dsimp [sA, sB, cellAt] <;> omega
      exact (hcDeleted (by simp [hca])).elim
    · have hc' : c = sV anchor := by
        calc
          c = ((sB anchor).1, (sB anchor).2 + 1) := h
          _ = sV anchor := by
            apply Prod.ext <;> dsimp [sV, sB, cellAt] <;> omega
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inl hc')
    · exfalso
      apply frame.southeast_not_mem
      have hc' : c = cellAt anchor 1 (-1) := by
        calc
          c = ((sB anchor).1, (sB anchor).2 - 1) := h
          _ = cellAt anchor 1 (-1) := by
            apply Prod.ext <;> dsimp [sB, cellAt] <;> omega
      simpa [hc'] using hc

/-! ## Connectivity after deleting marked cells -/

theorem edgeAdjacentIn_symm {cells : Finset Cell} {a b : Cell}
    (h : EdgeAdjacentIn cells a b) : EdgeAdjacentIn cells b a :=
  ⟨h.2.1, h.1, edgeAdjacent_symm h.2.2⟩

theorem reflTransGen_symm {r : Cell → Cell → Prop}
    (hsymm : ∀ {a b}, r a b → r b a) {a b : Cell}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
      exact (Relation.ReflTransGen.single (hsymm hbc)).trans ih

/-- In a connected set, after deleting finitely many cells, every remaining
component meets a prescribed seed union as soon as every edge exiting the
deleted set lands in that union. -/
theorem reaches_seedUnion_after_delete (P : Polyomino)
    (deleted seedUnion : Finset Cell) (seed0 : Cell)
    (hseed0Cells : seed0 ∈ P.cells)
    (hseed0Deleted : seed0 ∉ deleted)
    (hseed0Seed : seed0 ∈ seedUnion)
    (hboundary : ∀ {d c : Cell}, d ∈ deleted → c ∈ P.cells →
      c ∉ deleted → EdgeAdjacent d c → c ∈ seedUnion)
    {c : Cell} (hc : c ∈ P.cells \ deleted) :
    ∃ s, s ∈ seedUnion ∧
      Relation.ReflTransGen (EdgeAdjacentIn (P.cells \ deleted)) c s := by
  have hpath := P.edgeConnected seed0 hseed0Cells c
    (Finset.mem_sdiff.mp hc).1
  have forward : ∀ {z : Cell},
      Relation.ReflTransGen (EdgeAdjacentIn P.cells) seed0 z →
      z ∉ deleted →
      ∃ s, s ∈ seedUnion ∧
        Relation.ReflTransGen (EdgeAdjacentIn (P.cells \ deleted)) s z := by
    intro z hz
    induction hz with
    | refl =>
        intro _
        exact ⟨seed0, hseed0Seed, Relation.ReflTransGen.refl⟩
    | @tail y z hyz hstep ih =>
        intro hzDeleted
        by_cases hyDeleted : y ∈ deleted
        · have hzSeed := hboundary hyDeleted hstep.2.1 hzDeleted hstep.2.2
          exact ⟨z, hzSeed, Relation.ReflTransGen.refl⟩
        · rcases ih hyDeleted with ⟨s, hs, hsy⟩
          refine ⟨s, hs, hsy.tail ?_⟩
          exact ⟨Finset.mem_sdiff.mpr ⟨hstep.1, hyDeleted⟩,
            Finset.mem_sdiff.mpr ⟨hstep.2.1, hzDeleted⟩, hstep.2.2⟩
  rcases forward hpath (Finset.mem_sdiff.mp hc).2 with ⟨s, hs, hsc⟩
  exact ⟨s, hs, reflTransGen_symm edgeAdjacentIn_symm hsc⟩

def deletionSeedSystem (P : Polyomino) (deleted : Finset Cell)
    (seeds : Bool → Finset Cell)
    (hsubset : ∀ i, seeds i ⊆ P.cells \ deleted)
    (hnonempty : ∀ i, (seeds i).Nonempty)
    (hconnected : ∀ i, EdgeConnected (seeds i))
    (hdisjoint : Disjoint (seeds false) (seeds true))
    (seed0 : Cell) (hseed0 : seed0 ∈ seeds false)
    (hboundary : ∀ {d c : Cell}, d ∈ deleted → c ∈ P.cells →
      c ∉ deleted → EdgeAdjacent d c →
        c ∈ allSeedCells seeds) : SeedSystem Bool where
  cells := P.cells \ deleted
  seeds := seeds
  seed_subset := hsubset
  seed_nonempty := hnonempty
  seed_connected := hconnected
  seed_pairwise_disjoint := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hdisjoint
    · exact hdisjoint.symm
    · exact (hij rfl).elim
  reaches_seed := by
    intro c hc
    have hseed0Ambient := hsubset false hseed0
    rcases reaches_seedUnion_after_delete P deleted (allSeedCells seeds) seed0
        (Finset.mem_sdiff.mp hseed0Ambient).1
        (Finset.mem_sdiff.mp hseed0Ambient).2
        (mem_coveredCells.mpr ⟨false, hseed0⟩) hboundary hc with
      ⟨s, hs, hcs⟩
    rcases mem_coveredCells.mp hs with ⟨i, hsi⟩
    exact ⟨i, s, hsi, hcs⟩

theorem edgeConnected_singleton (a : Cell) :
    EdgeConnected ({a} : Finset Cell) := by
  intro x hx y hy
  simp only [Finset.mem_singleton] at hx hy
  subst x
  subst y
  exact Relation.ReflTransGen.refl

theorem edgeConnected_pair {a b : Cell} (hab : EdgeAdjacent a b) :
    EdgeConnected ({a, b} : Finset Cell) := by
  intro x hx y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨by simp, by simp, hab⟩
  · exact Relation.ReflTransGen.single ⟨by simp, by simp,
      edgeAdjacent_symm hab⟩
  · exact Relation.ReflTransGen.refl

theorem edgeConnected_triple {a b c : Cell}
    (hab : EdgeAdjacent a b) (hbc : EdgeAdjacent b c) :
    EdgeConnected ({a, b, c} : Finset Cell) := by
  intro x hx y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨by simp, by simp, hab⟩
  · exact (Relation.ReflTransGen.single
      ⟨by simp, by simp, hab⟩).tail ⟨by simp, by simp, hbc⟩
  · exact Relation.ReflTransGen.single ⟨by simp, by simp,
      edgeAdjacent_symm hab⟩
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨by simp, by simp, hbc⟩
  · exact (Relation.ReflTransGen.single
      ⟨by simp, by simp, edgeAdjacent_symm hbc⟩).tail
        ⟨by simp, by simp, edgeAdjacent_symm hab⟩
  · exact Relation.ReflTransGen.single ⟨by simp, by simp,
      edgeAdjacent_symm hbc⟩
  · exact Relation.ReflTransGen.refl

def chainSeed (cells : Finset Cell) (a b c : Cell) : Finset Cell :=
  if c ∈ cells then {a, b, c} else {a, b}

theorem mem_chainSeed_iff {cells : Finset Cell} {a b c x : Cell} :
    x ∈ chainSeed cells a b c ↔
      x = a ∨ x = b ∨ (x = c ∧ c ∈ cells) := by
  by_cases hc : c ∈ cells <;> simp [chainSeed, hc]

theorem chainSeed_subset {cells : Finset Cell} {a b c : Cell}
    (ha : a ∈ cells) (hb : b ∈ cells) :
    chainSeed cells a b c ⊆ cells := by
  intro x hx
  by_cases hc : c ∈ cells
  · simp only [chainSeed, hc, if_true, Finset.mem_insert,
      Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · simp only [chainSeed, hc, if_false, Finset.mem_insert,
      Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption

theorem chainSeed_nonempty (cells : Finset Cell) (a b c : Cell) :
    (chainSeed cells a b c).Nonempty := by
  by_cases hc : c ∈ cells
  · exact ⟨a, by simp [chainSeed, hc]⟩
  · exact ⟨a, by simp [chainSeed, hc]⟩

theorem chainSeed_connected {cells : Finset Cell} {a b c : Cell}
    (hab : EdgeAdjacent a b) (hbc : EdgeAdjacent b c) :
    EdgeConnected (chainSeed cells a b c) := by
  by_cases hc : c ∈ cells
  · rw [chainSeed, if_pos hc]
    exact edgeConnected_triple hab hbc
  · rw [chainSeed, if_neg hc]
    exact edgeConnected_pair hab

theorem cellAt_east (anchor : Cell) (dx dy : ℤ) :
    EdgeAdjacent (cellAt anchor dx dy) (cellAt anchor (dx + 1) dy) := by
  left
  apply Prod.ext <;> dsimp [cellAt] <;> omega

theorem cellAt_north (anchor : Cell) (dx dy : ℤ) :
    EdgeAdjacent (cellAt anchor dx dy) (cellAt anchor dx (dy + 1)) := by
  right; right; left
  apply Prod.ext <;> dsimp [cellAt] <;> omega

/-! ## The three seeded systems used by the convolution branches -/

def sSecondSeeds (anchor : Cell) : Bool → Finset Cell
  | false => {sU anchor}
  | true => {sB anchor}

def sFourthSeeds (anchor : Cell) : Bool → Finset Cell
  | false => {sU anchor, sV anchor}
  | true => {sR anchor}

def sFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    Bool → Finset Cell
  | false => chainSeed cells (sU anchor) (sV anchor) (sTopV anchor)
  | true => chainSeed cells (sR anchor) (sS anchor) (sTopS anchor)

theorem sU_mem_sFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    sU anchor ∈ sFifthSeeds cells anchor false := by
  by_cases h : sTopV anchor ∈ cells <;>
    simp [sFifthSeeds, chainSeed, h]

theorem sV_mem_sFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    sV anchor ∈ sFifthSeeds cells anchor false := by
  by_cases h : sTopV anchor ∈ cells <;>
    simp [sFifthSeeds, chainSeed, h]

theorem sR_mem_sFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    sR anchor ∈ sFifthSeeds cells anchor true := by
  by_cases h : sTopS anchor ∈ cells <;>
    simp [sFifthSeeds, chainSeed, h]

theorem sS_mem_sFifthSeeds (cells : Finset Cell) (anchor : Cell) :
    sS anchor ∈ sFifthSeeds cells anchor true := by
  by_cases h : sTopS anchor ∈ cells <;>
    simp [sFifthSeeds, chainSeed, h]

def sSecondSystem {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells) : SeedSystem Bool := by
  let P := x.1.toPolyomino
  let anchor := x.2.1
  let deleted : Finset Cell := {sA anchor}
  let seeds := sSecondSeeds anchor
  refine deletionSeedSystem P deleted seeds ?_ ?_ ?_ ?_ (sU anchor) ?_ ?_
  · intro i
    cases i
    · intro c hc
      have hc' : c = sU anchor := by simpa [seeds, sSecondSeeds] using hc
      subst c
      exact Finset.mem_sdiff.mpr ⟨hu, by
        simp [deleted, sA, sU]⟩
    · intro c hc
      have hc' : c = sB anchor := by simpa [seeds, sSecondSeeds] using hc
      subst c
      exact Finset.mem_sdiff.mpr ⟨by simpa [P, anchor, sB] using frame.b_mem,
        by simp [deleted, sA, sB]⟩
  · intro i
    cases i <;> simp [seeds, sSecondSeeds]
  · intro i
    cases i <;> simp only [seeds, sSecondSeeds]
    <;> apply edgeConnected_singleton
  · apply Finset.disjoint_left.mpr
    intro c hc0 hc1
    simp only [seeds, sSecondSeeds, Finset.mem_singleton] at hc0 hc1
    subst c
    exact sU_ne_sB anchor hc1
  · simp [seeds, sSecondSeeds]
  · intro d c hd hc hcDeleted hadj
    have hd' : d = sA anchor := by simpa [deleted] using hd
    subst d
    rcases s_a_neighbors frame hc hadj with rfl | rfl
    · apply mem_coveredCells.mpr
      refine ⟨true, ?_⟩
      simpa only [anchor] using
        (show sB anchor ∈ seeds true by simp [seeds, sSecondSeeds])
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor] using
        (show sU anchor ∈ seeds false by simp [seeds, sSecondSeeds])

@[simp]
theorem sSecondSystem_cells {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells) :
    (sSecondSystem x frame hu).cells =
      x.1.toPolyomino.cells \ {sA x.2.1} := by
  rfl

@[simp]
theorem sSecondSystem_seeds {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells) (i : Bool) :
    (sSecondSystem x frame hu).seeds i = sSecondSeeds x.2.1 i := by
  rfl

def sFourthSystem {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells) : SeedSystem Bool := by
  let P := x.1.toPolyomino
  let anchor := x.2.1
  let deleted : Finset Cell := {sA anchor, sB anchor}
  let seeds := sFourthSeeds anchor
  refine deletionSeedSystem P deleted seeds ?_ ?_ ?_ ?_ (sU anchor) ?_ ?_
  · intro i
    cases i
    · intro c hc
      simp only [seeds, sFourthSeeds, Finset.mem_insert,
        Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact Finset.mem_sdiff.mpr ⟨hu, by
          simp [deleted, sA, sU, sB]⟩
      · exact Finset.mem_sdiff.mpr ⟨hv, by
          simp [deleted, sV, sA, sB, cellAt]⟩
    · intro c hc
      have hc' : c = sR anchor := by simpa [seeds, sFourthSeeds] using hc
      subst c
      exact Finset.mem_sdiff.mpr ⟨hr, by
        simp [deleted, sR, sA, sB, cellAt]⟩
  · intro i
    cases i
    · exact ⟨sU anchor, by simp [seeds, sFourthSeeds]⟩
    · exact ⟨sR anchor, by simp [seeds, sFourthSeeds]⟩
  · intro i
    cases i
    · apply edgeConnected_pair
      simpa [sU, sV] using cellAt_east anchor 0 1
    · exact edgeConnected_singleton _
  · apply Finset.disjoint_left.mpr
    intro c hc0 hc1
    simp only [seeds, sFourthSeeds, Finset.mem_insert,
      Finset.mem_singleton] at hc0 hc1
    rcases hc0 with rfl | rfl
    <;> simp [sU, sV, sR, cellAt] at hc1
  · simp [seeds, sFourthSeeds]
  · intro d c hd hc hcDeleted hadj
    have hseed := s_lowerDomino_boundary frame hd hc hcDeleted hadj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hseed
    rcases hseed with rfl | rfl | rfl
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor] using
        (show sU anchor ∈ seeds false by simp [seeds, sFourthSeeds])
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor] using
        (show sV anchor ∈ seeds false by simp [seeds, sFourthSeeds])
    · apply mem_coveredCells.mpr
      refine ⟨true, ?_⟩
      simpa only [anchor] using
        (show sR anchor ∈ seeds true by simp [seeds, sFourthSeeds])

@[simp]
theorem sFourthSystem_cells {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells) :
    (sFourthSystem x frame hu hv hr).cells =
      x.1.toPolyomino.cells \ {sA x.2.1, sB x.2.1} := by
  rfl

@[simp]
theorem sFourthSystem_seeds {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells) (i : Bool) :
    (sFourthSystem x frame hu hv hr).seeds i = sFourthSeeds x.2.1 i := by
  rfl

def sFifthSystem {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : sS x.2.1 ∈ x.1.toPolyomino.cells) : SeedSystem Bool := by
  let P := x.1.toPolyomino
  let anchor := x.2.1
  let deleted : Finset Cell := {sA anchor, sB anchor}
  let ambient := P.cells \ deleted
  let seeds := sFifthSeeds ambient anchor
  refine deletionSeedSystem P deleted seeds ?_ ?_ ?_ ?_ (sU anchor) ?_ ?_
  · intro i
    cases i
    · apply chainSeed_subset
      · exact Finset.mem_sdiff.mpr ⟨hu, by
          simp [deleted, sA, sU, sB]⟩
      · exact Finset.mem_sdiff.mpr ⟨hv, by
          simp [deleted, sV, sA, sB, cellAt]⟩
    · apply chainSeed_subset
      · exact Finset.mem_sdiff.mpr ⟨hr, by
          simp [deleted, sR, sA, sB, cellAt]⟩
      · exact Finset.mem_sdiff.mpr ⟨hs, by
          simp [deleted, sS, sA, sB, cellAt]⟩
  · intro i
    cases i <;> apply chainSeed_nonempty
  · intro i
    cases i
    · apply chainSeed_connected
      · simpa [sU, sV] using cellAt_east anchor 0 1
      · simpa [sV, sTopV] using cellAt_north anchor 1 1
    · apply chainSeed_connected
      · simpa [sR, sS] using cellAt_north anchor 2 0
      · simpa [sS, sTopS] using cellAt_north anchor 2 1
  · apply Finset.disjoint_left.mpr
    intro c hc0 hc1
    have hc0' : c = sU anchor ∨ c = sV anchor ∨
        (c = sTopV anchor ∧ sTopV anchor ∈ ambient) := by
      exact (mem_chainSeed_iff.mp (show
        c ∈ chainSeed ambient (sU anchor) (sV anchor) (sTopV anchor) from hc0))
    have hc1' : c = sR anchor ∨ c = sS anchor ∨
        (c = sTopS anchor ∧ sTopS anchor ∈ ambient) := by
      exact (mem_chainSeed_iff.mp (show
        c ∈ chainSeed ambient (sR anchor) (sS anchor) (sTopS anchor) from hc1))
    rcases hc0' with h0 | h0 | ⟨h0, _⟩ <;>
      rcases hc1' with h1 | h1 | ⟨h1, _⟩ <;>
      have h := h0.symm.trans h1 <;>
      simp [sU, sV, sR, sS, sTopV, sTopS, cellAt] at h
  · simpa only [seeds] using sU_mem_sFifthSeeds ambient anchor
  · intro d c hd hc hcDeleted hadj
    have hseed := s_lowerDomino_boundary frame hd hc hcDeleted hadj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hseed
    rcases hseed with rfl | rfl | rfl
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor, seeds] using sU_mem_sFifthSeeds ambient anchor
    · apply mem_coveredCells.mpr
      refine ⟨false, ?_⟩
      simpa only [anchor, seeds] using sV_mem_sFifthSeeds ambient anchor
    · apply mem_coveredCells.mpr
      refine ⟨true, ?_⟩
      simpa only [anchor, seeds] using sR_mem_sFifthSeeds ambient anchor

@[simp]
theorem sFifthSystem_cells {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : sS x.2.1 ∈ x.1.toPolyomino.cells) :
    (sFifthSystem x frame hu hv hr hs).cells =
      x.1.toPolyomino.cells \ {sA x.2.1, sB x.2.1} := by
  rfl

@[simp]
theorem sFifthSystem_seeds {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : sS x.2.1 ∈ x.1.toPolyomino.cells) (i : Bool) :
    (sFifthSystem x frame hu hv hr hs).seeds i =
      sFifthSeeds (x.1.toPolyomino.cells \ {sA x.2.1, sB x.2.1}) x.2.1 i := by
  rfl

theorem sFifthSystem_sU_mem {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : sS x.2.1 ∈ x.1.toPolyomino.cells) :
    sU x.2.1 ∈ (sFifthSystem x frame hu hv hr hs).seeds false := by
  rw [sFifthSystem_seeds]
  exact sU_mem_sFifthSeeds _ _

theorem sFifthSystem_sV_mem {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : sS x.2.1 ∈ x.1.toPolyomino.cells) :
    sV x.2.1 ∈ (sFifthSystem x frame hu hv hr hs).seeds false := by
  rw [sFifthSystem_seeds]
  exact sV_mem_sFifthSeeds _ _

theorem sFifthSystem_sR_mem {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : sS x.2.1 ∈ x.1.toPolyomino.cells) :
    sR x.2.1 ∈ (sFifthSystem x frame hu hv hr hs).seeds true := by
  rw [sFifthSystem_seeds]
  exact sR_mem_sFifthSeeds _ _

theorem sFifthSystem_sS_mem {n : ℕ} (x : MarkedOccurrence .s n)
    (frame : SFrame x.1.toPolyomino.cells x.2.1)
    (hu : sU x.2.1 ∈ x.1.toPolyomino.cells)
    (hv : sV x.2.1 ∈ x.1.toPolyomino.cells)
    (hr : sR x.2.1 ∈ x.1.toPolyomino.cells)
    (hs : sS x.2.1 ∈ x.1.toPolyomino.cells) :
    sS x.2.1 ∈ (sFifthSystem x frame hu hv hr hs).seeds true := by
  rw [sFifthSystem_seeds]
  exact sS_mem_sFifthSeeds _ _

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

end GeometricFourFiveInternal

end LeanProofs.KlarnerConstant
