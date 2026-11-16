import AperiodicMonotile.HatData

namespace AperiodicMonotile

inductive MetaKind | H | T | P | F
  deriving DecidableEq, Repr, Fintype

structure Child where
  kind : MetaKind
  transformCode : Nat
  deriving DecidableEq, Repr

abbrev MetaPatch := List Child

/-- The fixed 29-placement scaffold from `isohedral/hatviz/hat.js`. -/
opaque scaffold29 : MetaPatch

/-- Child selections defining the next H,T,P,F supertiles. -/
opaque selectChildren : MetaKind → List (Fin 29)

/-- Substitution counts, rows indexed by parent and columns H,T,P,F. -/
def substCount : MetaKind → MetaKind → Nat
  | .H, .H => 3 | .H, .T => 1 | .H, .P => 3 | .H, .F => 3
  | .T, .H => 1 | .T, _ => 0
  | .P, .H => 2 | .P, .P => 1 | .P, .F => 2 | .P, .T => 0
  | .F, .H => 2 | .F, .P => 1 | .F, .F => 3 | .F, .T => 0

/-- Exact rational affine construction of one metatile generation. -/
opaque nextMetatiles : Nat → MetaKind → Nat

/-- Flatten a level-n decorated metatile into a finite list of hat placements. -/
opaque flatten : Nat → MetaKind → PatchCode

/-- Chosen H occurrence that makes the sequence coherent. -/
opaque embedH : Nat → Placement

/-- Normalize level n+1 so that the chosen level-n H child is literally fixed. -/
opaque nestedH : Nat → PatchCode

/-- Closed quasi-isometry constants of the elementary kite adjacency graph. -/
opaque gridConstant : Nat
opaque baseOffset : Nat

/-- Radius certified by substitution depth. -/
def certifiedRadius (n : Nat) : Nat := (n - baseOffset) / gridConstant

def coverLevel (r : Nat) : Nat := gridConstant * r + baseOffset

/-- Every generated object is a valid exact hat patch. -/
theorem nestedH_valid (n : Nat) : validPatchB hatPolygon (nestedH n) = true := by
  -- Induction on n; the step is the reflected 29-placement certificate.
  sorry

/-- Coherence of the local views. -/
theorem nestedH_subset (n : Nat) :
    ∀ t, t ∈ nestedH n → t ∈ nestedH (n+1) := by
  sorry

/-- The distinguished child is uniformly interior; radius tends to infinity. -/
theorem radius_growth (n : Nat) :
    certifiedRadius (coverLevel n) ≥ n := by
  -- The selected H child is one complete kite-adjacency layer inside its
  -- parent.  Induct on substitution depth, then use the finite periodic-grid
  -- path bound encoded by `gridConstant`.
  sorry

/-- Primitive-recursive tilability at every requested radius. -/
theorem hat_has_patch_covering (r : Nat) :
    ∃ n, validPatchB hatPolygon (nestedH n) = true ∧
         coversHexBallB hatPolygon (nestedH n) r = true := by
  refine ⟨coverLevel r, nestedH_valid (coverLevel r), ?_⟩
  -- use `radius_growth r` and the Boolean coverage specification
  sorry

end AperiodicMonotile
