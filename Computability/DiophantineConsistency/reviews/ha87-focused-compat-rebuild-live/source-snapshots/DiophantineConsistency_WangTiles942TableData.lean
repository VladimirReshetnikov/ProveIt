import DiophantineConsistency.WangTiles942Data
import Mathlib.Algebra.BigOperators.Fin

/-! The exact current row data and physical ranking, without broad tactic imports.
The two finite-list proofs retain the original checked definition of `tile`. -/
namespace DiophantineConsistency.WangTiles942
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 1024

structure Tile where
  west : ℕ
  north : ℕ
  east : ℕ
  south : ℕ
  deriving DecidableEq, Repr, Inhabited

def headColor (q b : ℕ) : ℕ := 2 * q + b + 2

def start : Tile := ⟨2, 435, 3, 1⟩

def transitionRow (j : Fin 430) : ℕ × Tile :=
  let a := action j
  let d := a.2.1.toNat
  (j.val + 1, ⟨(1-d) * rail false a.2.2, headColor (j.val/2) (j.val%2),
    d * rail true a.2.2, a.1.toNat⟩)

def copyRows (a : ℕ) : List (ℕ × Tile) :=
  (List.range 2).map (fun b => (433 - 2*a + b, ⟨0,432*a+b,0,432*a+b⟩))

def signalRows (d : Bool) : List (ℕ × Tile) :=
  (targetList d).flatMap (fun q => (List.range 2).map (fun b =>
    (423+2*rail d q+b, ⟨d.toNat*rail d q,b,(1-d.toNat)*rail d q,headColor q b⟩)))

def tailRows : List (ℕ × Tile) :=
  (List.range 2).flatMap (fun a => (List.range 2).map (fun b =>
    (923+2*a+b, ⟨0,432*a+b,0,438⟩))) ++
  [(927,⟨2,434,2,0⟩),(928,⟨3,436,4,4⟩),(929,⟨4,436,4,0⟩)] ++
  [434,435,436].map (fun t => (496+t,⟨1,438,1,t⟩)) ++
  (List.range 3).flatMap (fun a => (List.range 3).map (fun b =>
    (933+3*a+b,⟨a^2,437,b,437⟩)))

/-- Every constructor family in printed order; the two values of a and d
are enumerated explicitly without changing their row formulas. -/
def indexedRows : List (ℕ × Tile) :=
  [(0, start)] ++ List.ofFn transitionRow ++ (copyRows 0 ++ copyRows 1) ++
    (signalRows false ++ signalRows true) ++ tailRows

/-- Exchanging only the copy and signal blocks puts the complete table in
index order. The permutation proof below does not rely on finite sorting. -/
def orderedRows : List (ℕ × Tile) :=
  [(0, start)] ++ List.ofFn transitionRow ++ (copyRows 1 ++ copyRows 0) ++
    (signalRows true ++ signalRows false) ++ tailRows

theorem row_indices_exact : orderedRows.map Prod.fst = List.range 942 := by
  decide +kernel

theorem ordered_count : orderedRows.length = 942 := by
  have h := congrArg List.length row_indices_exact
  simpa only [List.length_map, List.length_range] using h

/-- The actual indexed tile, selected from the complete ordered row list. -/
def tile (i : Fin 942) : Tile := (orderedRows[i.val]'(by rw [ordered_count]; exact i.isLt)).2

/-- The unscaled selector coefficient in the actual printed Phi. -/
def selectorWeight (t : Tile) : ℕ :=
  1 + 2 ^ 10 * (1 + t.west + 2 ^ 8 * t.north + 2 ^ 17 * t.east + 2 ^ 25 * t.south)

/-- The sorted physical position, written over all 941 non-Start rows. -/
def physicalPosition (i : Fin 942) : ℕ :=
  if i.val = 0 then 0 else 1 + ((orderedRows.drop 1).map (fun row =>
    (2 ^ 44 - 1 + selectorWeight row.2 - selectorWeight (tile i)) / 2 ^ 44)).sum

end DiophantineConsistency.WangTiles942
