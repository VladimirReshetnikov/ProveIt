import KlarnerConstant.Polyomino

/-!
# Bui's seventeen square-lattice neighborhood patterns

This module transcribes the neighborhood table in Section 4 of Bui v2 into
finite required and forbidden offset sets.  Coordinates use the usual square
lattice orientation.  For every multi-cell pattern, `(0, 0)` is the leftmost
required cell in the principal row; the other diagrams are translated to that
anchor.  A blank position imposes no condition.

The already-proved `buiGPattern` is reused verbatim.  Consequently the
southwest-anchor theorems in `Polyomino.lean` apply directly to the `G`
coordinate of this table.
-/

namespace LeanProofs.KlarnerConstant

/-- Names of the seventeen neighborhoods in Bui's refined recurrence. -/
inductive BuiNeighborhood where
  | c | d | e | f | g | h | p | q | r | s | t | u | v | w | x | y | z
  deriving DecidableEq, Repr

/-- Explicit finite enumeration of Bui's seventeen neighborhood names. -/
instance : Fintype BuiNeighborhood where
  elems := {.c, .d, .e, .f, .g, .h, .p, .q, .r,
    .s, .t, .u, .v, .w, .x, .y, .z}
  complete kind := by cases kind <;> simp

/-- Type `C`: one required cell, with the two lateral cells and the southwest
semicircle of five cells forbidden. -/
def buiCPattern : OffsetPattern where
  required := {(0, 0)}
  forbidden := {(-1, 1), (1, 1), (-1, 0), (1, 0),
    (-1, -1), (0, -1), (1, -1)}

/-- Type `D`. -/
def buiDPattern : OffsetPattern where
  required := {(0, 0)}
  forbidden := {(-1, 1), (-1, 0), (1, 0),
    (-1, -1), (0, -1), (1, -1)}

/-- Type `E`. -/
def buiEPattern : OffsetPattern where
  required := {(0, 0)}
  forbidden := {(-1, 0), (1, 0), (-1, -1), (0, -1), (1, -1)}

/-- Type `F`. -/
def buiFPattern : OffsetPattern where
  required := {(0, 0)}
  forbidden := {(-1, -1), (0, -1), (1, -1)}

/-- Type `H`. -/
def buiHPattern : OffsetPattern where
  required := {(0, 0)}
  forbidden := {(-1, 1), (-1, 0), (-1, -1), (0, -1), (1, -1)}

/-- Type `P`: a horizontal required pair with the three cells below it and
the next southeastern cell forbidden. -/
def buiPPattern : OffsetPattern where
  required := {(0, 0), (1, 0)}
  forbidden := {(0, -1), (1, -1), (2, -1)}

/-- Type `Q`. -/
def buiQPattern : OffsetPattern where
  required := {(0, 0), (1, 0)}
  forbidden := {(-1, 0), (-1, -1), (0, -1), (1, -1)}

/-- Type `R`. -/
def buiRPattern : OffsetPattern where
  required := {(0, 0), (1, 0)}
  forbidden := {(-1, 1), (-1, 0),
    (-1, -1), (0, -1), (1, -1), (2, -1)}

/-- Type `S`. -/
def buiSPattern : OffsetPattern where
  required := {(0, 0), (1, 0)}
  forbidden := {(-1, 1), (-1, 0), (-1, -1), (0, -1), (1, -1)}

/-- Type `T`. -/
def buiTPattern : OffsetPattern where
  required := {(0, 0), (1, 0)}
  forbidden := {(-1, 0), (-1, -1), (0, -1), (1, -1), (2, -1)}

/-- Type `U`. -/
def buiUPattern : OffsetPattern where
  required := {(0, 0), (1, 0)}
  forbidden := {(-1, -1), (0, -1), (1, -1), (2, -1)}

/-- Type `V`. -/
def buiVPattern : OffsetPattern where
  required := {(0, 0), (1, 0), (2, 0)}
  forbidden := {(-1, 0), (-1, -1), (0, -1), (1, -1), (2, -1)}

/-- Type `W`. -/
def buiWPattern : OffsetPattern where
  required := {(0, 0), (1, 0), (2, 0)}
  forbidden := {(-1, 1), (-1, 0),
    (-1, -1), (0, -1), (1, -1), (2, -1)}

/-- Type `X`. -/
def buiXPattern : OffsetPattern where
  required := {(0, 0), (1, 0)}
  forbidden := {(-1, 0), (2, 0),
    (-1, -1), (0, -1), (1, -1), (2, -1)}

/-- Type `Y`. -/
def buiYPattern : OffsetPattern where
  required := {(0, 0), (1, 0)}
  forbidden := {(-1, 1), (-1, 0), (2, 0),
    (-1, -1), (0, -1), (1, -1), (2, -1)}

/-- Type `Z`. -/
def buiZPattern : OffsetPattern where
  required := {(0, 0), (1, 0)}
  forbidden := {(-1, 1), (2, 1), (-1, 0), (2, 0),
    (-1, -1), (0, -1), (1, -1), (2, -1)}

/-- The exact neighborhood associated with each coordinate name. -/
def BuiNeighborhood.pattern : BuiNeighborhood → OffsetPattern
  | .c => buiCPattern
  | .d => buiDPattern
  | .e => buiEPattern
  | .f => buiFPattern
  | .g => buiGPattern
  | .h => buiHPattern
  | .p => buiPPattern
  | .q => buiQPattern
  | .r => buiRPattern
  | .s => buiSPattern
  | .t => buiTPattern
  | .u => buiUPattern
  | .v => buiVPattern
  | .w => buiWPattern
  | .x => buiXPattern
  | .y => buiYPattern
  | .z => buiZPattern

/-- Count occurrences of one named Bui neighborhood in a polyomino. -/
noncomputable def BuiNeighborhood.occurrenceCount
    (kind : BuiNeighborhood) (P : Polyomino) : ℕ :=
  kind.pattern.occurrenceCount P.cells

@[simp] theorem BuiNeighborhood.pattern_g : BuiNeighborhood.g.pattern = buiGPattern := rfl

theorem one_le_buiNeighborhood_g_occurrenceCount (P : Polyomino) :
    1 ≤ BuiNeighborhood.g.occurrenceCount P :=
  one_le_gOccurrenceCount P

end LeanProofs.KlarnerConstant
