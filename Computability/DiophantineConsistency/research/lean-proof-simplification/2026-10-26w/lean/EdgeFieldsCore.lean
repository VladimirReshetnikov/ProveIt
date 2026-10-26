
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

#print axioms row_eq_of_edges
#print axioms row_fields_roundtrip
#print axioms grid_horizontal
#print axioms grid_temporal
#print axioms grid_eq_of_matching
end NewProofStructures.EdgeFields
