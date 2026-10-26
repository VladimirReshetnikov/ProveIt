import Lean.Elab.Tactic.Omega

/-!
Constructing rows from shared edge fields.
The four projections have the exact west/north/east/south order of the
production Wang tile. This generic module deliberately does not import the
942-tile table, and proves no new allowedness fact for that table.
-/
namespace NewProofStructures.EdgeFields

structure Tile (C : Type) where
  west : C
  north : C
  east : C
  south : C


theorem Tile.ext {C : Type} {a b : Tile C}
    (hw : a.west = b.west) (hn : a.north = b.north)
    (he : a.east = b.east) (hs : a.south = b.south) : a = b := by
  cases a; cases b; cases hw; cases hn; cases he; cases hs; rfl

def Horizontal {C : Type} (row : Int → Tile C) : Prop :=
  ∀ x, (row (x + 1)).west = (row x).east

/-- E is the color on the west edge; the east edge is the next value of E. -/
def rowOfEdges {C : Type} (E N S : Int → C) (x : Int) : Tile C :=
  ⟨E x, N x, E (x + 1), S x⟩

theorem rowOfEdges_horizontal {C : Type} (E N S : Int → C) :
    Horizontal (rowOfEdges E N S) := fun _ => rfl

/-- Every compatible row has this normal form; the reformulation loses no rows. -/
theorem row_eq_of_edges {C : Type} (row : Int → Tile C) (h : Horizontal row) :
    row = rowOfEdges (fun x => (row x).west)
      (fun x => (row x).north) (fun x => (row x).south) := by
  funext x
  apply Tile.ext <;> try rfl
  exact (h x).symm

/-- The inverse law in the field direction. Together with row_eq_of_edges,
    this gives the explicit bijection without a heavyweight equivalence import. -/
theorem row_fields_roundtrip {C : Type} (E N S : Int → C) :
    (fun x => (rowOfEdges E N S x).west) = E ∧
    (fun x => (rowOfEdges E N S x).north) = N ∧
    (fun x => (rowOfEdges E N S x).south) = S := ⟨rfl, rfl, rfl⟩

/-- An arbitrary time index and successor suffice, including a finite cyclic one. -/
def gridOfEdges {C σ : Type} (next : σ → σ)
    (E V : σ → Int → C) (k : σ) (x : Int) : Tile C :=
  ⟨E k x, V k x, E k (x + 1), V (next k) x⟩

theorem grid_horizontal {C σ : Type} (next : σ → σ)
    (E V : σ → Int → C) (k : σ) (x : Int) :
    (gridOfEdges next E V k (x + 1)).west =
      (gridOfEdges next E V k x).east := rfl

theorem grid_temporal {C σ : Type} (next : σ → σ)
    (E V : σ → Int → C) (k : σ) (x : Int) :
    (gridOfEdges next E V (next k) x).north =
      (gridOfEdges next E V k x).south := rfl

/-- Existing grid data can be put in edge normal form without changing any tile. -/
theorem grid_eq_of_matching {C σ : Type} (next : σ → σ) (T : σ → Int → Tile C)
    (hh : ∀ k x, (T k (x + 1)).west = (T k x).east)
    (ht : ∀ k x, (T (next k) x).north = (T k x).south) :
    T = gridOfEdges next (fun k x => (T k x).west)
      (fun k x => (T k x).north) := by
  funext k x
  apply Tile.ext <;> try rfl
  · exact (hh k x).symm
  · exact (ht k x).symm

/-- The initializer's exact four tuples, copied for a small migration test. -/
def literalInitial (x : Int) : Tile Nat :=
  if x < 0 then ⟨2,434,2,0⟩
  else if x = 0 then ⟨2,435,3,1⟩
  else if x = 1 then ⟨3,436,4,4⟩
  else ⟨4,436,4,0⟩

def initialE (x : Int) : Nat := if x ≤ 0 then 2 else if x = 1 then 3 else 4

def initialN (x : Int) : Nat := if x < 0 then 434 else if x = 0 then 435 else 436

def initialS (x : Int) : Nat := if x = 0 then 1 else if x = 1 then 4 else 0

theorem literalInitial_eq_edges : literalInitial = rowOfEdges initialE initialN initialS := by
  funext x
  by_cases hn : x < 0
  · have h0 : x ≠ 0 := by omega
    have h1 : x ≠ 1 := by omega
    have hl : x ≤ 0 := by omega
    have hnext : x + 1 ≤ 0 := by omega
    simp [literalInitial, rowOfEdges, initialE, initialN, initialS, hn, h0, h1, hl, hnext]
  · by_cases h0 : x = 0
    · subst x; rfl
    · by_cases h1 : x = 1
      · subst x; rfl
      · have hl : ¬ x ≤ 0 := by omega
        have hnext : ¬ x + 1 ≤ 0 := by omega
        have hnext1 : x + 1 ≠ 1 := by omega
        simp [literalInitial, rowOfEdges, initialE, initialN, initialS,
          hn, h0, h1, hl, hnext, hnext1]

theorem literalInitial_horizontal : Horizontal literalInitial := by
  rw [literalInitial_eq_edges]
  exact rowOfEdges_horizontal _ _ _

/-- The unrestricted literal transition/receive/pass pattern of stepTile. -/
def movedHead (h : Int) (d : Bool) : Int := if d then h + 1 else h - 1

def literalStep (h : Int) (d : Bool) (rail : Bool → Nat) (source written : Nat)
    (target : Nat → Nat) (bit : Int → Nat) (x : Int) : Tile Nat :=
  if x = h then ⟨(1-d.toNat) * rail false, source, d.toNat * rail true, written⟩
  else if x = movedHead h d then
    ⟨d.toNat * rail d, bit x, (1-d.toNat) * rail d, target (bit x)⟩
  else ⟨0, bit x, 0, bit x⟩

def stepE (h : Int) (d : Bool) (rail : Bool → Nat) (x : Int) : Nat :=
  if x = (if d then h + 1 else h) then rail d else 0

def stepN (h : Int) (source : Nat) (bit : Int → Nat) (x : Int) : Nat :=
  if x = h then source else bit x

def stepS (h : Int) (d : Bool) (written : Nat) (target : Nat → Nat)
    (bit : Int → Nat) (x : Int) : Nat :=
  if x = h then written else if x = movedHead h d then target (bit x) else bit x

/-- All four literal fields agree. No state or halting premise is needed. -/
theorem literalStep_eq_edges (h : Int) (d : Bool) (rail : Bool → Nat)
    (source written : Nat) (target : Nat → Nat) (bit : Int → Nat) :
    literalStep h d rail source written target bit =
      rowOfEdges (stepE h d rail) (stepN h source bit) (stepS h d written target bit) := by
  funext x
  cases d <;>
    simp only [literalStep, movedHead, stepE, stepN, stepS, rowOfEdges,
      Bool.false_eq_true, Bool.toNat_false, Bool.toNat_true, ite_false, ite_true,
      Nat.sub_zero, Nat.sub_self, Nat.one_mul, Nat.zero_mul]
  · by_cases ho : x = h
    · subst x
      simp [show h + 1 ≠ h by omega]
    · by_cases hn : x = h - 1
      · simp [hn, show h - 1 ≠ h by omega]
      · have he : x + 1 ≠ h := by omega
        simp [ho, hn, he]
  · by_cases ho : x = h
    · subst x
      simp [show h ≠ h + 1 by omega]
    · by_cases hn : x = h + 1
      · simp [hn, show h + 1 ≠ h by omega]
      · have he : x + 1 ≠ h + 1 := by omega
        simp [ho, hn, he]

theorem literalStep_horizontal (h : Int) (d : Bool) (rail : Bool → Nat)
    (source written : Nat) (target : Nat → Nat) (bit : Int → Nat) :
    Horizontal (literalStep h d rail source written target bit) := by
  rw [literalStep_eq_edges]
  exact rowOfEdges_horizontal _ _ _

#print axioms row_eq_of_edges
#print axioms row_fields_roundtrip
#print axioms grid_horizontal
#print axioms grid_temporal
#print axioms grid_eq_of_matching
#print axioms literalInitial_eq_edges
#print axioms literalStep_eq_edges
#print axioms literalStep_horizontal
end NewProofStructures.EdgeFields
