import KlarnerConstant.Polyomino
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Interval

/-!
# Finite counting of normalized polyominoes

This module turns the geometric `Polyomino` definition into finite counting
types.  A normalized `n`-cell polyomino has southwest anchor `(0, 0)` and
exactly `n` cells.

Finiteness is not assumed.  Edge-connectedness gives a walk from the origin to
each cell.  After lifting that walk to the finite induced graph on the
polyomino's cells and erasing loops, its length is less than the number of
cells.  Since a grid edge changes either coordinate by at most one, every cell
of a normalized `n`-cell polyomino lies in the finite square `[-n,n]²`.

Finally, `fixedPolyominoCount` counts normalized polyominoes and `gCount` sums
their type-G occurrences.  The inequality between them is the finite sum of
`one_le_gOccurrenceCount_normalize`.
-/

namespace LeanProofs.KlarnerConstant

/-- The undirected square grid as a simple graph. -/
private def squareGrid : SimpleGraph Cell where
  Adj := EdgeAdjacent
  symm := by
    constructor
    intro _ _ h
    exact edgeAdjacent_symm h
  loopless := by
    constructor
    intro a h
    rcases h with h | h | h | h
    · have h' := congrArg Prod.fst h
      dsimp at h'
      omega
    · have h' := congrArg Prod.fst h
      dsimp at h'
      omega
    · have h' := congrArg Prod.snd h
      dsimp at h'
      omega
    · have h' := congrArg Prod.snd h
      dsimp at h'
      omega

private theorem squareGrid_adj {a b : Cell} :
    squareGrid.Adj a b ↔ EdgeAdjacent a b :=
  Iff.rfl

/-- A grid edge changes each coordinate by at most one, in both directions. -/
private theorem edgeAdjacent_coordinateBounds {a b : Cell} (h : EdgeAdjacent a b) :
    b.1 - a.1 ≤ 1 ∧ a.1 - b.1 ≤ 1 ∧
      b.2 - a.2 ≤ 1 ∧ a.2 - b.2 ≤ 1 := by
  rcases h with h | h | h | h <;> subst b <;> norm_num

/-- Coordinate displacement along a grid walk is bounded by its length. -/
private theorem squareGrid_walk_coordinateBounds {a b : Cell}
    (w : squareGrid.Walk a b) :
    b.1 - a.1 ≤ (w.length : ℤ) ∧ a.1 - b.1 ≤ (w.length : ℤ) ∧
      b.2 - a.2 ≤ (w.length : ℤ) ∧ a.2 - b.2 ≤ (w.length : ℤ) := by
  induction w with
  | nil => norm_num
  | @cons a b c hab w ih =>
      have hab' : EdgeAdjacent a b := squareGrid_adj.mp hab
      rcases edgeAdjacent_coordinateBounds hab' with ⟨habx, hbax, haby, hbay⟩
      rcases ih with ⟨hwx, hxw, hwy, hyw⟩
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      constructor
      · omega
      constructor
      · omega
      constructor <;> omega

/-- An `EdgeConnected` witness produces a grid walk whose whole support stays
inside the given finite set. -/
private theorem exists_gridWalk_support_subset {s : Finset Cell} {a b : Cell}
    (ha : a ∈ s) (h : Relation.ReflTransGen (EdgeAdjacentIn s) a b) :
    ∃ w : squareGrid.Walk a b, ∀ c ∈ w.support, c ∈ s := by
  induction h with
  | refl =>
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      intro c hc
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hc
      subst c
      exact ha
  | @tail b c hab hbc ih =>
      rcases ih with ⟨w, hw⟩
      have hbcAdj : squareGrid.Adj b c := squareGrid_adj.mpr hbc.2.2
      refine ⟨w.concat hbcAdj, ?_⟩
      intro d hd
      rw [SimpleGraph.Walk.support_concat] at hd
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | rfl
      · exact hw d hd
      · exact hbc.2.1

namespace Polyomino

/-- Any two cells of a polyomino are joined by a simple grid path shorter than
the number of cells. -/
private theorem exists_short_gridWalk (P : Polyomino) {a b : Cell}
    (ha : a ∈ P.cells) (hb : b ∈ P.cells) :
    ∃ w : squareGrid.Walk a b, w.length < P.cells.card := by
  obtain ⟨w, hw⟩ :=
    exists_gridWalk_support_subset ha (P.edgeConnected a ha b hb)
  letI : Fintype {c // c ∈ (↑P.cells : Set Cell)} :=
    Fintype.ofFinset P.cells (by simp)
  let lifted := w.induce (↑P.cells : Set Cell) hw
  let path := lifted.toPath
  let mapped : squareGrid.Walk a b :=
    path.val.map
      (SimpleGraph.Embedding.induce (G := squareGrid) (↑P.cells : Set Cell)).toHom
  refine ⟨mapped, ?_⟩
  have hlength : path.val.length < Fintype.card {c // c ∈ P.cells} :=
    path.property.length_lt
  calc
    mapped.length = path.val.length := by
      exact SimpleGraph.Walk.length_map _ _
    _ < Fintype.card {c // c ∈ P.cells} := hlength
    _ = P.cells.card := by
      exact Fintype.card_ofFinset P.cells (by simp)

end Polyomino

/-- The finite square of lattice cells with both coordinates in `[-n,n]`. -/
noncomputable def coordinateBox (n : ℕ) : Finset Cell :=
  Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ)

/-- A polyomino with a fixed southwest anchor and a fixed number of cells. -/
structure NormalizedPolyomino (n : ℕ) where
  toPolyomino : Polyomino
  southwestAnchor_eq : toPolyomino.southwestAnchor = (0, 0)
  card_cells : toPolyomino.cells.card = n

namespace NormalizedPolyomino

@[ext]
theorem ext {n : ℕ} {P Q : NormalizedPolyomino n}
    (h : P.toPolyomino = Q.toPolyomino) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- The origin is a cell of every normalized polyomino. -/
theorem origin_mem {n : ℕ} (P : NormalizedPolyomino n) :
    (0, 0) ∈ P.toPolyomino.cells := by
  rw [← P.southwestAnchor_eq]
  exact P.toPolyomino.southwestAnchor_mem

/-- Every cell of a normalized `n`-cell polyomino lies in `[-n,n]²`. -/
theorem cell_mem_coordinateBox {n : ℕ} (P : NormalizedPolyomino n)
    {c : Cell} (hc : c ∈ P.toPolyomino.cells) : c ∈ coordinateBox n := by
  obtain ⟨w, hw⟩ := P.toPolyomino.exists_short_gridWalk P.origin_mem hc
  rw [P.card_cells] at hw
  have hwle : w.length ≤ n := Nat.le_of_lt hw
  have hwle' : (w.length : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast hwle
  have hcoord := squareGrid_walk_coordinateBounds w
  simp only [sub_zero, zero_sub] at hcoord
  simp only [coordinateBox, Finset.mem_product, Finset.mem_Icc]
  rcases hcoord with ⟨hxp, hxn, hyp, hyn⟩
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- Encode the cell set as a finset in the universal finite coordinate box. -/
private noncomputable def cellCode {n : ℕ} (P : NormalizedPolyomino n) :
    Finset {c // c ∈ coordinateBox n} :=
  Finset.univ.filter fun c ↦ c.1 ∈ P.toPolyomino.cells

private theorem cellCode_injective (n : ℕ) :
    Function.Injective (cellCode : NormalizedPolyomino n →
      Finset {c // c ∈ coordinateBox n}) := by
  intro P Q hcode
  apply NormalizedPolyomino.ext
  apply Polyomino.ext
  ext c
  constructor
  · intro hc
    have hcbox := P.cell_mem_coordinateBox hc
    have hm : (⟨c, hcbox⟩ : {d // d ∈ coordinateBox n}) ∈ cellCode P := by
      simp [cellCode, hc]
    rw [hcode] at hm
    simpa [cellCode] using hm
  · intro hc
    have hcbox := Q.cell_mem_coordinateBox hc
    have hm : (⟨c, hcbox⟩ : {d // d ∈ coordinateBox n}) ∈ cellCode Q := by
      simp [cellCode, hc]
    rw [← hcode] at hm
    simpa [cellCode] using hm

/-- There are only finitely many normalized `n`-cell polyominoes. -/
instance finite (n : ℕ) : Finite (NormalizedPolyomino n) :=
  Finite.of_injective
    (cellCode : NormalizedPolyomino n →
      Finset {c // c ∈ coordinateBox n})
    (cellCode_injective n)

/-- A noncomputable enumeration, obtained from the proved `Finite` instance. -/
noncomputable instance fintype (n : ℕ) : Fintype (NormalizedPolyomino n) :=
  Fintype.ofFinite _

end NormalizedPolyomino

/-- The number of normalized fixed polyominoes with exactly `n` cells. -/
noncomputable def fixedPolyominoCount (n : ℕ) : ℕ :=
  Fintype.card (NormalizedPolyomino n)

/-- The total number of anchored type-G occurrences over all normalized
`n`-cell polyominoes. -/
noncomputable def gCount (n : ℕ) : ℕ :=
  ∑ P : NormalizedPolyomino n,
    buiGPattern.occurrenceCount P.toPolyomino.cells

/-- Every normalized polyomino supplies at least one type-G occurrence. -/
theorem fixedPolyominoCount_le_gCount (n : ℕ) :
    fixedPolyominoCount n ≤ gCount n := by
  classical
  unfold fixedPolyominoCount gCount
  have hsum :
      (∑ _P : NormalizedPolyomino n, 1) ≤
        ∑ P : NormalizedPolyomino n,
          buiGPattern.occurrenceCount P.toPolyomino.cells := by
    exact Finset.sum_le_sum fun P _ ↦
      one_le_gOccurrenceCount P.toPolyomino
  simpa only [Fintype.card, Finset.card_eq_sum_ones] using hsum

end LeanProofs.KlarnerConstant
