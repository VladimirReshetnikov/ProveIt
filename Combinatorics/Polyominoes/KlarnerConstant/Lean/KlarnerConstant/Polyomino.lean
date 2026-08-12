import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Data.Prod.Lex
import Mathlib.Logic.Relation
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Polyomino geometry for Klarner's constant

This file gives the geometric definitions needed by the recurrence proof for
Klarner's constant.  A cell is an integer lattice point, with edge adjacency
given by the four unit coordinate steps.  A polyomino is a finite, nonempty,
edge-connected set of cells.

The last part formalizes the elementary observation connecting ordinary
polyominoes to Bui's type `G`: the leftmost cell in the bottom row has no cell
immediately to its left or in any of the three positions in the row below.
Patterns are represented independently of `G` by finite sets of required and
forbidden offsets.
-/

namespace LeanProofs.KlarnerConstant

/-- A cell of the square lattice. -/
abbrev Cell := ℤ × ℤ

/-- Edge adjacency on the square lattice. -/
def EdgeAdjacent (a b : Cell) : Prop :=
  b = (a.1 + 1, a.2) ∨ b = (a.1 - 1, a.2) ∨
  b = (a.1, a.2 + 1) ∨ b = (a.1, a.2 - 1)

theorem edgeAdjacent_symm {a b : Cell} (h : EdgeAdjacent a b) : EdgeAdjacent b a := by
  rcases h with h | h | h | h <;> subst b <;> simp [EdgeAdjacent]

theorem edgeAdjacent_translate {a b : Cell} (v : Cell) (h : EdgeAdjacent a b) :
    EdgeAdjacent (v + a) (v + b) := by
  rcases h with h | h | h | h <;> subst b
  · left
    apply Prod.ext <;> dsimp <;> omega
  · right; left
    apply Prod.ext <;> dsimp <;> omega
  · right; right; left
    apply Prod.ext <;> dsimp <;> omega
  · right; right; right
    apply Prod.ext <;> dsimp <;> omega

theorem edgeAdjacent_translate_iff {a b : Cell} (v : Cell) :
    EdgeAdjacent (v + a) (v + b) ↔ EdgeAdjacent a b := by
  constructor
  · intro h
    have h' := edgeAdjacent_translate (-v) h
    simpa [add_assoc] using h'
  · exact edgeAdjacent_translate v

/-- The edge-adjacency relation induced on a finite set of cells. -/
def EdgeAdjacentIn (s : Finset Cell) (a b : Cell) : Prop :=
  a ∈ s ∧ b ∈ s ∧ EdgeAdjacent a b

/-- Every two cells in `s` are joined by an edge path that stays in `s`. -/
def EdgeConnected (s : Finset Cell) : Prop :=
  ∀ a, a ∈ s → ∀ b, b ∈ s →
    Relation.ReflTransGen (EdgeAdjacentIn s) a b

/-- A finite, nonempty, edge-connected square-lattice animal (polyomino). -/
structure Polyomino where
  cells : Finset Cell
  nonempty : cells.Nonempty
  edgeConnected : EdgeConnected cells

/-- `LatticeAnimal` is a synonym for `Polyomino`. -/
abbrev LatticeAnimal := Polyomino

namespace Polyomino

@[ext]
theorem ext {P Q : Polyomino} (h : P.cells = Q.cells) : P = Q := by
  cases P
  cases Q
  simp_all

private theorem edgeConnected_translate {s : Finset Cell} (hs : EdgeConnected s) (v : Cell) :
    EdgeConnected (s.image fun c ↦ v + c) := by
  intro a ha b hb
  rcases Finset.mem_image.mp ha with ⟨a₀, ha₀, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨b₀, hb₀, rfl⟩
  apply Relation.ReflTransGen.lift (fun c ↦ v + c) (r := EdgeAdjacentIn s)
  · intro x y hxy
    exact ⟨Finset.mem_image.mpr ⟨x, hxy.1, rfl⟩,
      Finset.mem_image.mpr ⟨y, hxy.2.1, rfl⟩,
      edgeAdjacent_translate v hxy.2.2⟩
  · exact hs a₀ ha₀ b₀ hb₀

/-- Translate every cell of a polyomino by the lattice vector `v`. -/
def translate (P : Polyomino) (v : Cell) : Polyomino where
  cells := P.cells.image fun c ↦ v + c
  nonempty := P.nonempty.image _
  edgeConnected := edgeConnected_translate P.edgeConnected v

@[simp]
theorem cells_translate (P : Polyomino) (v : Cell) :
    (P.translate v).cells = P.cells.image fun c ↦ v + c := rfl

theorem mem_translate_cells {P : Polyomino} {v c : Cell} :
    c ∈ (P.translate v).cells ↔ c - v ∈ P.cells := by
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨d, hd, rfl⟩
    convert hd using 1
    ext <;> simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  · intro hc
    apply Finset.mem_image.mpr
    refine ⟨c - v, hc, ?_⟩
    ext <;> simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

/-- Lexicographic key `(y,x)`, so its least value is bottommost, then leftmost. -/
private def southwestKey (c : Cell) : ℤ ×ₗ ℤ :=
  toLex (c.2, c.1)

/-- Convert a `(y,x)` key back to the cell `(x,y)`. -/
private def cellOfSouthwestKey (k : ℤ ×ₗ ℤ) : Cell :=
  ((ofLex k).2, (ofLex k).1)

private theorem cellOfSouthwestKey_key (c : Cell) :
    cellOfSouthwestKey (southwestKey c) = c := by
  rfl

/-- The unique leftmost cell in the bottom row. -/
noncomputable def southwestAnchor (P : Polyomino) : Cell :=
  cellOfSouthwestKey
    ((P.cells.image southwestKey).min' (P.nonempty.image southwestKey))

theorem southwestAnchor_mem (P : Polyomino) : P.southwestAnchor ∈ P.cells := by
  let keys := P.cells.image southwestKey
  have hkeys : keys.Nonempty := P.nonempty.image southwestKey
  have hmin : keys.min' hkeys ∈ keys := Finset.min'_mem keys hkeys
  rcases Finset.mem_image.mp hmin with ⟨c, hc, hckey⟩
  have hanchor : P.southwestAnchor = c := by
    unfold southwestAnchor
    change cellOfSouthwestKey (keys.min' hkeys) = c
    rw [← hckey]
    exact cellOfSouthwestKey_key c
  rwa [hanchor]

theorem southwestAnchor_min_y (P : Polyomino) {c : Cell} (hc : c ∈ P.cells) :
    P.southwestAnchor.2 ≤ c.2 := by
  let keys := P.cells.image southwestKey
  have hkeys : keys.Nonempty := P.nonempty.image southwestKey
  have hmem : southwestKey c ∈ keys := Finset.mem_image.mpr ⟨c, hc, rfl⟩
  have hle : keys.min' hkeys ≤ southwestKey c := Finset.min'_le keys _ hmem
  have hy := Prod.Lex.monotone_fst _ _ hle
  change (ofLex (keys.min' hkeys)).1 ≤ c.2 at hy
  simpa only [southwestAnchor, keys, hkeys, cellOfSouthwestKey] using hy

theorem southwestAnchor_min_x (P : Polyomino) {c : Cell} (hc : c ∈ P.cells)
    (hrow : P.southwestAnchor.2 = c.2) : P.southwestAnchor.1 ≤ c.1 := by
  let keys := P.cells.image southwestKey
  have hkeys : keys.Nonempty := P.nonempty.image southwestKey
  have hmem : southwestKey c ∈ keys := Finset.mem_image.mpr ⟨c, hc, rfl⟩
  have hle : keys.min' hkeys ≤ southwestKey c := Finset.min'_le keys _ hmem
  have hlex := (Prod.Lex.le_iff').mp hle
  have hfirst : (ofLex (keys.min' hkeys)).1 = c.2 := by
    simpa only [southwestAnchor, keys, hkeys, cellOfSouthwestKey] using hrow
  have hx := hlex.2 hfirst
  change (ofLex (keys.min' hkeys)).2 ≤ c.1 at hx
  simpa only [southwestAnchor, keys, hkeys, cellOfSouthwestKey] using hx

/-- `a` is bottommost in `P`, and leftmost among the bottommost cells. -/
def IsSouthwestAnchor (P : Polyomino) (a : Cell) : Prop :=
  a ∈ P.cells ∧
    (∀ c ∈ P.cells, a.2 ≤ c.2) ∧
    (∀ c ∈ P.cells, a.2 = c.2 → a.1 ≤ c.1)

theorem southwestAnchor_isSouthwest (P : Polyomino) :
    P.IsSouthwestAnchor P.southwestAnchor := by
  exact ⟨P.southwestAnchor_mem, fun _ hc ↦ P.southwestAnchor_min_y hc,
    fun _ hc hrow ↦ P.southwestAnchor_min_x hc hrow⟩

theorem isSouthwestAnchor_unique (P : Polyomino) {a b : Cell}
    (ha : P.IsSouthwestAnchor a) (hb : P.IsSouthwestAnchor b) : a = b := by
  have hy : a.2 = b.2 := le_antisymm (ha.2.1 b hb.1) (hb.2.1 a ha.1)
  have hx : a.1 = b.1 :=
    le_antisymm (ha.2.2 b hb.1 hy) (hb.2.2 a ha.1 hy.symm)
  exact Prod.ext hx hy

theorem existsUnique_isSouthwestAnchor (P : Polyomino) :
    ∃! a, P.IsSouthwestAnchor a :=
  ⟨P.southwestAnchor, P.southwestAnchor_isSouthwest,
    fun _ ha ↦ P.isSouthwestAnchor_unique ha P.southwestAnchor_isSouthwest⟩

theorem IsSouthwestAnchor.translate {P : Polyomino} {a : Cell}
    (ha : P.IsSouthwestAnchor a) (v : Cell) :
    (P.translate v).IsSouthwestAnchor (v + a) := by
  refine ⟨Finset.mem_image.mpr ⟨a, ha.1, rfl⟩, ?_, ?_⟩
  · intro c hc
    rcases Finset.mem_image.mp hc with ⟨d, hd, rfl⟩
    change v.2 + a.2 ≤ v.2 + d.2
    simpa [add_comm] using add_le_add_left (ha.2.1 d hd) v.2
  · intro c hc hrow
    rcases Finset.mem_image.mp hc with ⟨d, hd, rfl⟩
    have hy : a.2 = d.2 := by
      change v.2 + a.2 = v.2 + d.2 at hrow
      exact add_left_cancel hrow
    change v.1 + a.1 ≤ v.1 + d.1
    simpa [add_comm] using add_le_add_left (ha.2.2 d hd hy) v.1

theorem southwestAnchor_translate (P : Polyomino) (v : Cell) :
    (P.translate v).southwestAnchor = v + P.southwestAnchor := by
  apply (P.translate v).isSouthwestAnchor_unique
  · exact (P.translate v).southwestAnchor_isSouthwest
  · exact P.southwestAnchor_isSouthwest.translate v

/-- Translate a polyomino so that its southwest anchor is the origin. -/
noncomputable def normalize (P : Polyomino) : Polyomino :=
  P.translate (-P.southwestAnchor)

@[simp]
theorem southwestAnchor_normalize (P : Polyomino) :
    P.normalize.southwestAnchor = (0, 0) := by
  rw [normalize, southwestAnchor_translate]
  apply Prod.ext <;> simp

@[simp]
theorem origin_mem_normalize (P : Polyomino) : (0, 0) ∈ P.normalize.cells := by
  rw [← P.southwestAnchor_normalize]
  exact P.normalize.southwestAnchor_mem

theorem southwestAnchor_west_not_mem (P : Polyomino) :
    (P.southwestAnchor.1 - 1, P.southwestAnchor.2) ∉ P.cells := by
  intro hmem
  have hx := P.southwestAnchor_min_x hmem rfl
  omega

theorem southwestAnchor_southwest_not_mem (P : Polyomino) :
    (P.southwestAnchor.1 - 1, P.southwestAnchor.2 - 1) ∉ P.cells := by
  intro hmem
  have hy := P.southwestAnchor_min_y hmem
  omega

theorem southwestAnchor_south_not_mem (P : Polyomino) :
    (P.southwestAnchor.1, P.southwestAnchor.2 - 1) ∉ P.cells := by
  intro hmem
  have hy := P.southwestAnchor_min_y hmem
  omega

theorem southwestAnchor_southeast_not_mem (P : Polyomino) :
    (P.southwestAnchor.1 + 1, P.southwestAnchor.2 - 1) ∉ P.cells := by
  intro hmem
  have hy := P.southwestAnchor_min_y hmem
  omega

end Polyomino

/-- A finite local pattern, represented relative to a prospective anchor cell. -/
structure OffsetPattern where
  required : Finset Cell
  forbidden : Finset Cell
  deriving DecidableEq

namespace OffsetPattern

/-- All required offsets are occupied and all forbidden offsets are empty. -/
def OccursAt (pattern : OffsetPattern) (cells : Finset Cell) (anchor : Cell) : Prop :=
  (∀ offset ∈ pattern.required, anchor + offset ∈ cells) ∧
  (∀ offset ∈ pattern.forbidden, anchor + offset ∉ cells)

/-- The occupied cells which serve as anchors of occurrences of `pattern`. -/
noncomputable def occurrenceAnchors (pattern : OffsetPattern) (cells : Finset Cell) : Finset Cell := by
  classical
  exact cells.filter fun anchor ↦ pattern.OccursAt cells anchor

/-- The number of anchored occurrences of `pattern` in `cells`. -/
noncomputable def occurrenceCount (pattern : OffsetPattern) (cells : Finset Cell) : ℕ :=
  (pattern.occurrenceAnchors cells).card

end OffsetPattern

/-- Bui's type-G pattern: its anchor is occupied, while the cell to the left
and the three cells in the row below are forbidden. -/
def buiGPattern : OffsetPattern where
  required := {(0, 0)}
  forbidden := {(-1, 0), (-1, -1), (0, -1), (1, -1)}

theorem buiGPattern_occursAt_southwestAnchor (P : Polyomino) :
    buiGPattern.OccursAt P.cells P.southwestAnchor := by
  constructor
  · intro offset hoffset
    have hoffset' : offset = (0, 0) := by
      simpa [buiGPattern] using hoffset
    subst offset
    rw [show P.southwestAnchor + (0, 0) = P.southwestAnchor by
      apply Prod.ext <;> simp]
    exact P.southwestAnchor_mem
  · intro offset hoffset
    simp only [buiGPattern, Finset.mem_insert, Finset.mem_singleton] at hoffset
    rcases hoffset with h | h | h | h
    · subst offset
      rw [show P.southwestAnchor + (-1, 0) =
          (P.southwestAnchor.1 - 1, P.southwestAnchor.2) by
        apply Prod.ext <;> simp [sub_eq_add_neg]]
      exact P.southwestAnchor_west_not_mem
    · subst offset
      rw [show P.southwestAnchor + (-1, -1) =
          (P.southwestAnchor.1 - 1, P.southwestAnchor.2 - 1) by
        apply Prod.ext <;> simp [sub_eq_add_neg]]
      exact P.southwestAnchor_southwest_not_mem
    · subst offset
      rw [show P.southwestAnchor + (0, -1) =
          (P.southwestAnchor.1, P.southwestAnchor.2 - 1) by
        apply Prod.ext <;> simp [sub_eq_add_neg]]
      exact P.southwestAnchor_south_not_mem
    · subst offset
      rw [show P.southwestAnchor + (1, -1) =
          (P.southwestAnchor.1 + 1, P.southwestAnchor.2 - 1) by
        apply Prod.ext <;> simp [sub_eq_add_neg]]
      exact P.southwestAnchor_southeast_not_mem

/-- In the canonical normalization, the type-G occurrence is anchored at the origin. -/
theorem buiGPattern_occursAt_origin_normalize (P : Polyomino) :
    buiGPattern.OccursAt P.normalize.cells (0, 0) := by
  rw [← P.southwestAnchor_normalize]
  exact buiGPattern_occursAt_southwestAnchor P.normalize

theorem southwestAnchor_mem_gOccurrenceAnchors (P : Polyomino) :
    P.southwestAnchor ∈ buiGPattern.occurrenceAnchors P.cells := by
  classical
  exact Finset.mem_filter.mpr
    ⟨P.southwestAnchor_mem, buiGPattern_occursAt_southwestAnchor P⟩

/-- Every polyomino contributes at least one type-G occurrence. -/
theorem gOccurrenceAnchors_nonempty (P : Polyomino) :
    (buiGPattern.occurrenceAnchors P.cells).Nonempty :=
  ⟨P.southwestAnchor, southwestAnchor_mem_gOccurrenceAnchors P⟩

/-- Counting anchored occurrences, every polyomino contributes at least one `G`. -/
theorem one_le_gOccurrenceCount (P : Polyomino) :
    1 ≤ buiGPattern.occurrenceCount P.cells := by
  rw [OffsetPattern.occurrenceCount, Finset.one_le_card]
  exact gOccurrenceAnchors_nonempty P

/-- Every normalized polyomino contributes at least one type-G occurrence. -/
theorem one_le_gOccurrenceCount_normalize (P : Polyomino) :
    1 ≤ buiGPattern.occurrenceCount P.normalize.cells :=
  one_le_gOccurrenceCount P.normalize

end LeanProofs.KlarnerConstant
