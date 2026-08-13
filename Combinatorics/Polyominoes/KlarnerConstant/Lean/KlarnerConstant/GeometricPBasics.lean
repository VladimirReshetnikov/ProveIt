import KlarnerConstant.GeometricProfile

/-!
# Coordinate and orientation infrastructure for the P recurrence

This module isolates the lattice-coordinate, local-branch, and square-grid
orientation definitions used by the geometric proof of Bui's P recurrence.
-/

namespace LeanProofs.KlarnerConstant

/-! ## Lattice coordinates and the five local cases -/

/-- A cell at an integer offset from an anchor. -/
def pCell (anchor : Cell) (dx dy : ℤ) : Cell :=
  anchor + (dx, dy)

@[simp]
theorem pCell_zero (anchor : Cell) : pCell anchor 0 0 = anchor := by
  apply Prod.ext <;> dsimp [pCell] <;> omega

/-- The notation used by `OffsetPattern.OccursAt` is definitionally the same
as `pCell`; naming the bridge lets local simplification normalize mixed
geometric formulas without unfolding all coordinate arithmetic. -/
theorem add_offset_eq_pCell (anchor : Cell) (dx dy : ℤ) :
    anchor + (dx, dy) = pCell anchor dx dy := by
  rfl

@[simp]
theorem pCell_add (anchor : Cell) (dx dy ex ey : ℤ) :
    pCell (pCell anchor dx dy) ex ey =
      pCell anchor (dx + ex) (dy + ey) := by
  apply Prod.ext <;> dsimp [pCell] <;> omega

theorem pCell_injective (anchor : Cell) :
    Function.Injective (fun d : Cell ↦ anchor + d) :=
  add_right_injective anchor

@[simp]
theorem pCell_fst (anchor : Cell) (dx dy : ℤ) :
    (pCell anchor dx dy).1 = anchor.1 + dx := by
  rfl

@[simp]
theorem pCell_snd (anchor : Cell) (dx dy : ℤ) :
    (pCell anchor dx dy).2 = anchor.2 + dy := by
  rfl

/-- Coordinate arithmetic in the branch proofs is always arithmetic on the
two offsets; exposing that fact as a simp lemma avoids relying on reduction of
the product additive-group instance. -/
@[simp]
theorem pCell_add_offset (anchor : Cell) (dx dy ex ey : ℤ) :
    pCell anchor dx dy + (ex, ey) =
      pCell anchor (dx + ex) (dy + ey) := by
  apply Prod.ext <;> dsimp [pCell] <;> omega

@[simp]
theorem pCell_eq_pCell_iff (anchor : Cell) (dx dy ex ey : ℤ) :
    pCell anchor dx dy = pCell anchor ex ey ↔ dx = ex ∧ dy = ey := by
  constructor
  · intro h
    have hp : (dx, dy) = (ex, ey) := pCell_injective anchor h
    exact ⟨by simpa using congrArg Prod.fst hp,
      by simpa using congrArg Prod.snd hp⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp]
theorem pCell_eq_anchor_iff (anchor : Cell) (dx dy : ℤ) :
    pCell anchor dx dy = anchor ↔ dx = 0 ∧ dy = 0 := by
  constructor
  · intro h
    have h' : pCell anchor dx dy = pCell anchor 0 0 := by
      simpa only [pCell_zero] using h
    exact (pCell_eq_pCell_iff anchor dx dy 0 0).mp h'
  · rintro ⟨rfl, rfl⟩
    exact pCell_zero anchor

@[simp]
theorem anchor_eq_pCell_iff (anchor : Cell) (dx dy : ℤ) :
    anchor = pCell anchor dx dy ↔ dx = 0 ∧ dy = 0 := by
  simpa only [eq_comm] using pCell_eq_anchor_iff anchor dx dy

/-- The five mutually exclusive occupancy states used in the displayed
`P(n)` expansion. -/
inductive PBranch where
  | topLeftAbsent
  | topLeftOnly
  | firstColumn
  | firstColumnTopRight
  | fullRectangle
  deriving DecidableEq, Repr, Fintype

/-- The branch determined by the four cells `(0,1)`, `(1,1)`, `(0,2)`,
`(1,2)` above a marked `P` domino. -/
def pBranchAt (cells : Finset Cell) (anchor : Cell) : PBranch :=
  if pCell anchor 0 1 ∉ cells then .topLeftAbsent
  else if pCell anchor 1 1 ∉ cells then .topLeftOnly
  else if pCell anchor 0 2 ∉ cells then .firstColumn
  else if pCell anchor 1 2 ∉ cells then .firstColumnTopRight
  else .fullRectangle

theorem pBranchAt_cases (cells : Finset Cell) (anchor : Cell) :
    (pBranchAt cells anchor = .topLeftAbsent ∧
      pCell anchor 0 1 ∉ cells) ∨
    (pBranchAt cells anchor = .topLeftOnly ∧
      pCell anchor 0 1 ∈ cells ∧ pCell anchor 1 1 ∉ cells) ∨
    (pBranchAt cells anchor = .firstColumn ∧
      pCell anchor 0 1 ∈ cells ∧ pCell anchor 1 1 ∈ cells ∧
      pCell anchor 0 2 ∉ cells) ∨
    (pBranchAt cells anchor = .firstColumnTopRight ∧
      pCell anchor 0 1 ∈ cells ∧ pCell anchor 0 2 ∈ cells ∧
      pCell anchor 1 1 ∈ cells ∧ pCell anchor 1 2 ∉ cells) ∨
    (pBranchAt cells anchor = .fullRectangle ∧
      pCell anchor 0 1 ∈ cells ∧ pCell anchor 0 2 ∈ cells ∧
      pCell anchor 1 1 ∈ cells ∧ pCell anchor 1 2 ∈ cells) := by
  unfold pBranchAt
  by_cases h01 : pCell anchor 0 1 ∈ cells
  · simp only [h01, not_true_eq_false, if_false]
    by_cases h11 : pCell anchor 1 1 ∈ cells
    · simp only [h11, not_true_eq_false, if_false]
      by_cases h02 : pCell anchor 0 2 ∈ cells
      · simp only [h02, not_true_eq_false, if_false]
        by_cases h12 : pCell anchor 1 2 ∈ cells <;> simp [h12]
      · simp [h02]
    · simp [h11]
  · simp [h01]

/-! ## Signed coordinate permutations -/

/-- An explicit symmetry of the square lattice.  `map` converts the physical
orientation used by a branch into Bui's standard orientation. -/
structure GridOrientation where
  map : Cell → Cell
  inv : Cell → Cell
  map_zero : map 0 = 0
  map_add : ∀ a b, map (a + b) = map a + map b
  inv_map : Function.LeftInverse inv map
  map_inv : Function.RightInverse inv map
  edge : ∀ {a b}, EdgeAdjacent a b → EdgeAdjacent (map a) (map b)

namespace GridOrientation

theorem map_injective (o : GridOrientation) : Function.Injective o.map :=
  by
    intro a b hab
    calc
      a = o.inv (o.map a) := (o.inv_map a).symm
      _ = o.inv (o.map b) := congrArg o.inv hab
      _ = b := o.inv_map b

/-- Apply an orientation around the origin to a cell set. -/
def mapCells (o : GridOrientation) (cells : Finset Cell) : Finset Cell :=
  cells.image o.map

theorem mem_mapCells (o : GridOrientation) {cells : Finset Cell} {c : Cell} :
    o.map c ∈ o.mapCells cells ↔ c ∈ cells := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨d, hd, hdc⟩
    have hdc' : d = c := o.map_injective hdc
    subst d
    exact hd
  · exact fun h ↦ Finset.mem_image.mpr ⟨c, h, rfl⟩

@[simp]
theorem card_mapCells (o : GridOrientation) (cells : Finset Cell) :
    (o.mapCells cells).card = cells.card := by
  exact Finset.card_image_of_injective cells o.map_injective

theorem edgeConnected_mapCells (o : GridOrientation) {cells : Finset Cell}
    (h : EdgeConnected cells) : EdgeConnected (o.mapCells cells) := by
  intro a ha b hb
  rcases Finset.mem_image.mp ha with ⟨a₀, ha₀, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨b₀, hb₀, rfl⟩
  apply Relation.ReflTransGen.lift o.map
  · intro x y (hxy : EdgeAdjacentIn cells x y)
    exact ⟨Finset.mem_image.mpr ⟨x, hxy.1, rfl⟩,
      Finset.mem_image.mpr ⟨y, hxy.2.1, rfl⟩, o.edge hxy.2.2⟩
  · exact h a₀ ha₀ b₀ hb₀

/-- Rotate physical coordinates clockwise by ninety degrees. -/
def clockwise : GridOrientation where
  map := fun c ↦ (c.2, -c.1)
  inv := fun c ↦ (-c.2, c.1)
  map_zero := by apply Prod.ext <;> dsimp <;> omega
  map_add := by intro a b; apply Prod.ext <;> dsimp <;> omega
  inv_map := by intro a; apply Prod.ext <;> dsimp <;> omega
  map_inv := by intro a; apply Prod.ext <;> dsimp <;> omega
  edge := by
    intro a b h
    rcases h with h | h | h | h <;> subst b
    · right; right; right; apply Prod.ext <;> dsimp <;> omega
    · right; right; left; apply Prod.ext <;> dsimp <;> omega
    · left; apply Prod.ext <;> dsimp <;> omega
    · right; left; apply Prod.ext <;> dsimp <;> omega

/-- Reflect physical coordinates across the main diagonal. -/
def diagonal : GridOrientation where
  map := fun c ↦ (c.2, c.1)
  inv := fun c ↦ (c.2, c.1)
  map_zero := by apply Prod.ext <;> dsimp <;> omega
  map_add := by intro a b; apply Prod.ext <;> dsimp <;> omega
  inv_map := by intro a; rfl
  map_inv := by intro a; rfl
  edge := by
    intro a b h
    rcases h with h | h | h | h <;> subst b
    · right; right; left; apply Prod.ext <;> dsimp <;> omega
    · right; right; right; apply Prod.ext <;> dsimp <;> omega
    · left; apply Prod.ext <;> dsimp <;> omega
    · right; left; apply Prod.ext <;> dsimp <;> omega

/-- Reflect physical coordinates across the anti-diagonal. -/
def antiDiagonal : GridOrientation where
  map := fun c ↦ (-c.2, -c.1)
  inv := fun c ↦ (-c.2, -c.1)
  map_zero := by apply Prod.ext <;> dsimp <;> omega
  map_add := by intro a b; apply Prod.ext <;> dsimp <;> omega
  inv_map := by intro a; apply Prod.ext <;> dsimp <;> omega
  map_inv := by intro a; apply Prod.ext <;> dsimp <;> omega
  edge := by
    intro a b h
    rcases h with h | h | h | h <;> subst b
    · right; right; right; apply Prod.ext <;> dsimp <;> omega
    · right; right; left; apply Prod.ext <;> dsimp <;> omega
    · right; left; apply Prod.ext <;> dsimp <;> omega
    · left; apply Prod.ext <;> dsimp <;> omega

/-- The identity orientation. -/
def identity : GridOrientation where
  map := id
  inv := id
  map_zero := rfl
  map_add := by intro _ _; rfl
  inv_map := by intro a; rfl
  map_inv := by intro a; rfl
  edge := fun h ↦ h

@[simp] theorem clockwise_inv (c : Cell) :
    clockwise.inv c = (-c.2, c.1) := rfl

@[simp] theorem diagonal_inv (c : Cell) :
    diagonal.inv c = (c.2, c.1) := rfl

@[simp] theorem antiDiagonal_inv (c : Cell) :
    antiDiagonal.inv c = (-c.2, -c.1) := rfl

@[simp] theorem identity_inv (c : Cell) : identity.inv c = c := rfl

@[simp] theorem clockwise_map (c : Cell) :
    clockwise.map c = (c.2, -c.1) := rfl

@[simp] theorem diagonal_map (c : Cell) :
    diagonal.map c = (c.2, c.1) := rfl

@[simp] theorem antiDiagonal_map (c : Cell) :
    antiDiagonal.map c = (-c.2, -c.1) := rfl

@[simp] theorem identity_map (c : Cell) : identity.map c = c := rfl

end GridOrientation

@[simp]
theorem pCell_add_clockwise_inv (anchor : Cell) (dx dy ex ey : ℤ) :
    pCell anchor dx dy + GridOrientation.clockwise.inv (ex, ey) =
      pCell anchor (dx - ey) (dy + ex) := by
  apply Prod.ext <;> dsimp [pCell, GridOrientation.clockwise] <;> omega

@[simp]
theorem pCell_add_diagonal_inv (anchor : Cell) (dx dy ex ey : ℤ) :
    pCell anchor dx dy + GridOrientation.diagonal.inv (ex, ey) =
      pCell anchor (dx + ey) (dy + ex) := by
  apply Prod.ext <;> dsimp [pCell, GridOrientation.diagonal] <;> omega

@[simp]
theorem pCell_add_antiDiagonal_inv (anchor : Cell) (dx dy ex ey : ℤ) :
    pCell anchor dx dy + GridOrientation.antiDiagonal.inv (ex, ey) =
      pCell anchor (dx - ey) (dy - ex) := by
  apply Prod.ext <;> dsimp [pCell, GridOrientation.antiDiagonal] <;> omega

@[simp]
theorem pCell_add_identity_inv (anchor : Cell) (dx dy ex ey : ℤ) :
    pCell anchor dx dy + GridOrientation.identity.inv (ex, ey) =
      pCell anchor (dx + ex) (dy + ey) := by
  apply Prod.ext <;> dsimp [pCell, GridOrientation.identity] <;> omega

end LeanProofs.KlarnerConstant
