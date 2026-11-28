import Lib.Base

/-!
# Monotone paths through two square grids, and their turns

The combinatorics of the paths along which forms are moved through the two grids of unitary groups,
the grid of the `Y^i_j` and the grid of the `Ỹ^i_j`. Here only the indices occur.

A path goes from `(m, 0)` to `(0, m)` by steps up (`j` grows) or left (`i` falls) and meets the
diagonal once, at some `(l, l)`. Its first half lies in the grid of the `Ỹ` and its second half in
that of the `Y`. Both halves are recorded in one shape, as paths from `(0, m)` to `(l, l)` by steps
down or right. The half in the grid of the `Y` is read backwards, the way conjugate forms move. The
half in the grid of the `Ỹ` is read forwards, the way forms move, with the two indices exchanged: a
step left is recorded as a step down, and a step up as a step right.

## Main definitions and results

* `New.GridPath`: a monotone path in one grid. `New.TwoGridPath`: a path through both grids, given
  by two halves that meet on the diagonal.
* `New.TwoGridPath.Turn`: a turn replaces a node `(i, j)` by `(i + 1, j + 1)`.
* `New.TwoGridPath.exists_turn`: every path but the last can be turned.
* `New.TwoGridPath.turn_induction`: induction backwards along turns, one at each `(i, j)` with
  `i, j < m`, from the last path to the first.
-/

noncomputable section

namespace New

open Finset

/-- A monotone path in a grid from the node `(a₀, b₀)` to the node `(a, b)`: each step lowers the
second index or raises the first. -/
inductive GridPath (a₀ b₀ : ℕ) : ℕ → ℕ → Type
  /-- The path without steps. -/
  | nil : GridPath a₀ b₀ a₀ b₀
  /-- A path followed by the step from `(a, b + 1)` to `(a, b)`. -/
  | down {a b : ℕ} (p : GridPath a₀ b₀ a (b + 1)) : GridPath a₀ b₀ a b
  /-- A path followed by the step from `(a, b)` to `(a + 1, b)`. -/
  | right {a b : ℕ} (p : GridPath a₀ b₀ a b) : GridPath a₀ b₀ (a + 1) b

namespace GridPath

variable {a₀ b₀ a b a' b' m : ℕ}

/-- One path followed by another. -/
def append (p : GridPath a₀ b₀ a b) : ∀ {a' b' : ℕ}, GridPath a b a' b' → GridPath a₀ b₀ a' b'
  | _, _, nil => p
  | _, _, down q => (p.append q).down
  | _, _, right q => (p.append q).right

/-- The path down the first column, from `(0, m)` to `(0, b)`. -/
def column (hb : b ≤ m) : GridPath 0 m 0 b :=
  Nat.decreasingInduction (motive := fun b _ ↦ GridPath 0 m 0 b) (fun _ _ p ↦ p.down) nil hb

/-- The path along the row `m`, from `(0, m)` to `(a, m)`. -/
def row (m : ℕ) : ∀ a : ℕ, GridPath 0 m a m
  | 0 => nil
  | a + 1 => (row m a).right

/-- The unit squares between the first column and the steps down of a path, each named by its
corner with the least indices: the step from `(a, b + 1)` to `(a, b)` contributes the `(i, b)` with
`i < a`. -/
def squares : ∀ {a b : ℕ}, GridPath a₀ b₀ a b → Finset (ℕ × ℕ)
  | _, _, nil => ∅
  | a, b, down p => p.squares ∪ range a ×ˢ {b}
  | _, _, right p => p.squares

lemma column_self : column (le_refl m) = nil := by
  rw [column, Nat.decreasingInduction_self]

/-- The path down the first column from `(0, m)` to `(0, b)`, for `b < m`, is the one to
`(0, b + 1)` followed by a step down. -/
lemma column_of_lt (hb : b < m) : column hb.le = (column hb).down := by
  rw [column, column, Nat.decreasingInduction_succ_left (smn := hb)]

/-- Along a path from `(a₀, b₀)` to `(a, b)` the first index does not fall and the second does
not grow. -/
lemma le_and_le (p : GridPath a₀ b₀ a b) : a₀ ≤ a ∧ b ≤ b₀ := by
  induction p <;> omega

/-- The only path from `(0, m)` to `(a, m)` is `row m a`, the one that stays in the row `m`. -/
lemma eq_row (p : GridPath 0 m a m) : p = row m a := by
  have h_no_down {k : ℕ} (q : GridPath 0 m k (m + 1)) : False := by grind [q.le_and_le]
  induction a with
  | zero =>
    cases p with
    | nil => rfl
    | down q => exact (h_no_down q).elim
  | succ a ih =>
    cases p with
    | down q => exact (h_no_down q).elim
    | right q => rw [row, ih q]

/-- The squares to the left of the steps down of `p` followed by `q` are those of `p` and those
of `q`. -/
lemma squares_append (p : GridPath a₀ b₀ a b) (q : GridPath a b a' b') :
    (p.append q).squares = p.squares ∪ q.squares := by
  induction q <;> simp [append, squares, *]

/-- A square `s` to the left of a step down of a path from `(a₀, b₀)` to `(a, b)` lies to the left
of the column `a` and between the rows `b` and `b₀`. -/
lemma bounds_of_mem_squares {p : GridPath a₀ b₀ a b} {s : ℕ × ℕ} (hs : s ∈ p.squares) :
    s.1 < a ∧ b ≤ s.2 ∧ s.2 < b₀ := by
  induction p with
  | nil => simp [squares] at hs
  | down p ih => grind [squares, p.le_and_le]
  | right p ih => grind [squares]

/-- The path along a row has no step down, hence no squares. -/
lemma squares_row (m a : ℕ) : (row m a).squares = ∅ := by
  induction a <;> simp [row, squares, *]

/-- Let a path follow `q` to `(i, j + 1)`, step down to `(i, j)`, step right to `(i + 1, j)` and
follow `r`. Then the unit square with lower left corner `(i, j)` is not among the `squares` of the
path, the unit squares to the left of its steps down. -/
lemma notMem_squares_down_right_append {i j : ℕ} (q : GridPath a₀ b₀ i (j + 1))
    (r : GridPath (i + 1) j a b) : (i, j) ∉ (q.down.right.append r).squares := by
  have hq : (i, j) ∉ q.squares := by grind [→ bounds_of_mem_squares]
  have hr : (i, j) ∉ r.squares := by grind [→ bounds_of_mem_squares]
  simp [squares_append, squares, hq, hr]

/-- Let a path follow `q` to `(i, j + 1)`, go to `(i + 1, j)` in two steps and follow `r`. If it
passes through `(i + 1, j + 1)` instead of `(i, j)`, then its set of `squares`, the unit squares to
the left of its steps down, gains the square with lower left corner `(i, j)`. -/
lemma squares_right_down_append {i j : ℕ} (q : GridPath a₀ b₀ i (j + 1))
    (r : GridPath (i + 1) j a b) :
    (q.right.down.append r).squares = insert (i, j) (q.down.right.append r).squares := by
  have h_strip : range (i + 1) ×ˢ {j} = insert (i, j) (range i ×ˢ {j}) := by grind
  simp [squares_append, squares, h_strip]

/-- A path from `(a₀, b₀)` to `(a, b)` has a corner `(i, j)`, where it comes down and leaves to the
right, or ends with a step down, or has no step down (`b = b₀`). -/
lemma exists_corner_or_eq_down_or_eq (p : GridPath a₀ b₀ a b) :
    (∃ (i j : ℕ) (q : GridPath a₀ b₀ i (j + 1)) (r : GridPath (i + 1) j a b),
      p = q.down.right.append r) ∨
    (∃ q : GridPath a₀ b₀ a (b + 1), p = q.down) ∨
    b = b₀ := by
  induction p with
  | nil => exact .inr (.inr rfl)
  | down p _ => exact .inr (.inl ⟨p, rfl⟩)
  | @right a b p ih =>
    obtain ⟨i, j, q, r, rfl⟩ | ⟨q, rfl⟩ | hb := ih
    · exact .inl ⟨i, j, q, r.right, rfl⟩
    · exact .inl ⟨a, b, q, nil, rfl⟩
    · exact .inr (.inr hb)

end GridPath

/-- A path from `(m, 0)` to `(0, m)` by steps up or left, through the two grids. It meets the
diagonal at `(l, l)` with `l = diagonalIndex`. Both halves are recorded as paths from `(0, m)` to
`(l, l)`: `half false` is the part after the diagonal read backwards, in the grid of the `Y`, where
`(a, b)` is `Y^a_b`, and `half true` is the part before the diagonal with the two indices
exchanged, in the grid of the `Ỹ`, where `(a, b)` is `Ỹ^b_a`. -/
structure TwoGridPath (m : ℕ) where
  /-- The index `l` of the node `(l, l)` at which the path meets the diagonal. -/
  diagonalIndex : ℕ
  /-- The halves in the two grids, each recorded as a path from `(0, m)` to the diagonal node. -/
  half : Bool → GridPath 0 m diagonalIndex diagonalIndex

namespace TwoGridPath

variable {m : ℕ} {Γ Γ' : TwoGridPath m} {s : ℕ × ℕ}

/-- The first path, through `(0, 0)`: it goes left from `Ỹ^m_0` to `Ỹ^0_0` and up from `Y^0_0` to
`Y^0_m`, so both halves are recorded as going down the first column. -/
def first (m : ℕ) : TwoGridPath m := ⟨0, fun _ : Bool ↦ .column m.zero_le⟩

/-- The last path, through `(m, m)`: it goes up from `Ỹ^m_0` to `Ỹ^m_m` and left from `Y^m_m` to
`Y^0_m`, so both halves are recorded as going along the row `m`. -/
def last (m : ℕ) : TwoGridPath m := ⟨m, fun _ : Bool ↦ .row m m⟩

/-- `Turn Γ (i, j) Γ'`: the path `Γ` reaches `(i, j)` from the right and leaves it upwards, and `Γ'`
arises from `Γ` by replacing the node `(i, j)` by `(i + 1, j + 1)`. -/
inductive Turn : TwoGridPath m → ℕ × ℕ → TwoGridPath m → Prop
  /-- A turn off the diagonal, at a corner `(a, b)` where one half comes down and leaves to the
  right. For `half true` the node has the indices `(b, a)`. -/
  | inner (Γ : TwoGridPath m) (z : Bool) {a b : ℕ} (q : GridPath 0 m a (b + 1))
      (r : GridPath (a + 1) b Γ.diagonalIndex Γ.diagonalIndex)
      (hΓ : Γ.half z = q.down.right.append r) :
      Turn Γ (bif z then (b, a) else (a, b))
        ⟨Γ.diagonalIndex, Function.update Γ.half z (q.right.down.append r)⟩
  /-- A turn on the diagonal: both halves end with a step down. -/
  | diagonal {j : ℕ} (q : Bool → GridPath 0 m j (j + 1)) :
      Turn ⟨j, fun z : Bool ↦ (q z).down⟩ (j, j) ⟨j + 1, fun z : Bool ↦ (q z).right⟩

/-- The unit squares between the first path and `Γ`, each named by its corner with the least
indices: the `(i, j)` with `i, j < Γ.diagonalIndex`, the squares of `Γ.half false`, and the mirror
images in the diagonal of the squares of `Γ.half true`. -/
def squares (Γ : TwoGridPath m) : Finset (ℕ × ℕ) :=
  range Γ.diagonalIndex ×ˢ range Γ.diagonalIndex ∪ (Γ.half false).squares ∪
    (Γ.half true).squares.image Prod.swap

/-- The unit square with least corner `s` lies between the first path, through `(0, 0)`, and the
path `Γ` if and only if both indices of `s` are less than `Γ.diagonalIndex`, or `s` lies to the left
of a step down of `Γ.half false`, or its mirror image `s.swap` lies to the left of a step down of
`Γ.half true`. -/
lemma mem_squares : s ∈ Γ.squares ↔
    (s.1 < Γ.diagonalIndex ∧ s.2 < Γ.diagonalIndex) ∨
    s ∈ (Γ.half false).squares ∨
    s.swap ∈ (Γ.half true).squares := by
  grind [squares]

/-- A path from `(m, 0)` to `(0, m)` meets the diagonal at a node with indices at most `m`. -/
lemma diagonalIndex_le (Γ : TwoGridPath m) : Γ.diagonalIndex ≤ m := (Γ.half false).le_and_le.2

/-- Let `Γ` be a path from `(m, 0)` to `(0, m)` by steps up or left. The set `Γ.squares` of unit
squares between `Γ` and the path `first m` through `(0, 0)`, each named by its corner `(i, j)` with
the least indices, has only members with `i, j < m`. -/
lemma squares_subset (Γ : TwoGridPath m) : Γ.squares ⊆ range m ×ˢ range m := by
  rintro ⟨i, j⟩ hs
  suffices i < m ∧ j < m by simpa
  have hl : Γ.diagonalIndex ≤ m := Γ.diagonalIndex_le
  obtain ⟨hi : i < Γ.diagonalIndex, hj : j < Γ.diagonalIndex⟩ | h_false | h_true :=
    mem_squares.mp hs
  · omega
  · obtain ⟨hi : i < Γ.diagonalIndex, -, hj : j < m⟩ := GridPath.bounds_of_mem_squares h_false
    omega
  · obtain ⟨hj : j < Γ.diagonalIndex, -, hi : i < m⟩ := GridPath.bounds_of_mem_squares h_true
    omega

/-- No unit square lies between the first path, through `(0, 0)`, and itself. -/
lemma squares_first : (first m).squares = ∅ := by
  grind [squares, first, → GridPath.bounds_of_mem_squares]

/-- For the last path `last m`, the one through `(m, m)`, the set `(last m).squares` is exactly the
`(i, j)` with `i, j < m`, that is `range m ×ˢ range m`. -/
lemma squares_last : (last m).squares = range m ×ˢ range m := by
  simp [squares, last, GridPath.squares_row]

/-- Let `Γ` and `Γ'` be paths in `TwoGridPath m` with `Γ.Turn s Γ'`. Then `s ∉ Γ.squares`, and
`Γ'.squares` is `Γ.squares` with `s` inserted. -/
lemma Turn.squares_eq (h_turn : Γ.Turn s Γ') :
    s ∉ Γ.squares ∧ Γ'.squares = insert s Γ.squares := by
  cases h_turn with
  | @inner _ z a b q r hΓ =>
    obtain ⟨-, hb : Γ.diagonalIndex ≤ b⟩ := r.le_and_le
    have h_notMem : (a, b) ∉ (Γ.half z).squares := by
      simpa [hΓ] using GridPath.notMem_squares_down_right_append q r
    have h_notMem_swap (z' : Bool) : (b, a) ∉ (Γ.half z').squares := by
      grind [→ GridPath.bounds_of_mem_squares]
    have h_insert : (q.right.down.append r).squares = insert (a, b) (Γ.half z).squares := by
      simp [hΓ, GridPath.squares_right_down_append]
    constructor
    · cases z <;> simp [mem_squares, hb.not_gt, h_notMem, h_notMem_swap]
    · cases z <;> simp [squares, h_insert]
  | @diagonal j q =>
    have h_notMem (z : Bool) : (j, j) ∉ (q z).down.squares :=
      fun h_mem ↦ lt_irrefl j (GridPath.bounds_of_mem_squares h_mem).1
    have h_block : range (j + 1) ×ˢ range (j + 1) = insert (j, j)
        (range j ×ˢ range j ∪ range j ×ˢ {j} ∪ (range j ×ˢ {j}).image Prod.swap) := by
      rw [image_swap_product]
      grind
    refine ⟨by simp [mem_squares, h_notMem], ?_⟩
    simp only [squares, GridPath.squares, h_block, image_union, insert_union]
    ac_rfl

/-- If a path from `(m, 0)` to `(0, m)` has a turn at the node `s = (i, j)`, then `i, j < m`. -/
lemma Turn.mem_product (h_turn : Γ.Turn s Γ') : s ∈ range m ×ˢ range m := by
  obtain ⟨-, h_eq⟩ := h_turn.squares_eq
  exact Γ'.squares_subset (by simp [h_eq])

/-- Let `Γ'` arise from `Γ`, a path from `(m, 0)` to `(0, m)` by steps up or left, by replacing the
node `(i, j)` by `(i + 1, j + 1)`, where `i < j`. The turn takes place in `Γ.half false`, the part
of `Γ` after the diagonal node `(Γ.diagonalIndex, Γ.diagonalIndex)`, read backwards from `(0, m)`.
This half splits as a path `q` to `(i, j + 1)`, a step down, a step right and a path `r` to the
diagonal. The path `Γ'` has these two steps exchanged, and has the same diagonal node and the same
other half. -/
lemma Turn.exists_corner_of_lt {i j : ℕ} (h_turn : Γ.Turn (i, j) Γ') (hij : i < j) :
    ∃ (q : GridPath 0 m i (j + 1)) (r : GridPath (i + 1) j Γ.diagonalIndex Γ.diagonalIndex),
      Γ.half false = q.down.right.append r ∧
      Γ' = ⟨Γ.diagonalIndex, Function.update Γ.half false (q.right.down.append r)⟩ := by
  generalize hs : (i, j) = s at h_turn
  cases h_turn with
  | @inner _ z a b q r hΓ =>
    have hab : a + 1 ≤ Γ.diagonalIndex ∧ Γ.diagonalIndex ≤ b := r.le_and_le
    cases z <;> cases hs
    · exact ⟨q, r, hΓ, rfl⟩
    · omega
  | diagonal q => grind

/-- Let `Γ'` arise from `Γ`, a path from `(m, 0)` to `(0, m)` by steps up or left, by replacing the
node `(i, j)` by `(i + 1, j + 1)`, where `j < i`. The turn takes place in `Γ.half true`, the part
of `Γ` from `(m, 0)` to the diagonal node `(Γ.diagonalIndex, Γ.diagonalIndex)`, recorded with the
two indices exchanged, so that the node `(i, j)` appears as `(j, i)`. This half splits as a path
`q` to `(j, i + 1)`, a step down, a step right and a path `r` to the diagonal. The path `Γ'` has
these two steps exchanged, and has the same diagonal node and the same other half. -/
lemma Turn.exists_half_true_eq_of_gt {i j : ℕ} (h_turn : Γ.Turn (i, j) Γ') (hji : j < i) :
    ∃ (q : GridPath 0 m j (i + 1)) (r : GridPath (j + 1) i Γ.diagonalIndex Γ.diagonalIndex),
      Γ.half true = q.down.right.append r ∧
      Γ' = ⟨Γ.diagonalIndex, Function.update Γ.half true (q.right.down.append r)⟩ := by
  generalize hs : (i, j) = s at h_turn
  cases h_turn with
  | @inner _ z a b q r hΓ =>
    have hab : a + 1 ≤ Γ.diagonalIndex ∧ Γ.diagonalIndex ≤ b := r.le_and_le
    cases z <;> cases hs
    · omega
    · exact ⟨q, r, hΓ, rfl⟩
  | diagonal q => grind

/-- A turn at `(j, j)` takes place on the diagonal: both halves reach `(j, j + 1)`, and their last
step, down to `(j, j)`, is replaced by the step right to `(j + 1, j + 1)`. -/
lemma Turn.exists_eq_down_and_eq_right {j : ℕ} (h_turn : Γ.Turn (j, j) Γ') :
    ∃ q : Bool → GridPath 0 m j (j + 1),
      Γ = ⟨j, fun z : Bool ↦ (q z).down⟩ ∧
      Γ' = ⟨j + 1, fun z : Bool ↦ (q z).right⟩ := by
  generalize hs : (j, j) = s at h_turn
  cases h_turn with
  | @inner _ z a b q r hΓ =>
    have hab : a + 1 ≤ Γ.diagonalIndex ∧ Γ.diagonalIndex ≤ b := r.le_and_le
    grind
  | diagonal q =>
    cases hs
    exact ⟨q, rfl, rfl⟩

/-- Every path `Γ` from `(m, 0)` to `(0, m)` by steps up or left, other than `last m`, has a
turn. -/
lemma exists_turn (hΓ : Γ ≠ last m) : ∃ (s : ℕ × ℕ) (Γ' : TwoGridPath m), Γ.Turn s Γ' := by
  by_cases h_corner : ∃ (z : Bool) (a b : ℕ) (q : GridPath 0 m a (b + 1))
      (r : GridPath (a + 1) b Γ.diagonalIndex Γ.diagonalIndex), Γ.half z = q.down.right.append r
  · obtain ⟨z, a, b, q, r, h_eq⟩ := h_corner
    exact ⟨_, _, .inner Γ z q r h_eq⟩
  obtain ⟨l, half⟩ := Γ
  obtain rfl | hl := eq_or_ne l m
  · obtain rfl : half = fun _ : Bool ↦ .row l l := funext fun z ↦ (half z).eq_row
    exact absurd rfl hΓ
  -- Without corners, and below the last row, both halves end with a step down.
  have h_down (z : Bool) : ∃ q : GridPath 0 m l (l + 1), half z = q.down := by
    obtain h_has_corner | h_ends_down | h_last_row := (half z).exists_corner_or_eq_down_or_eq
    · exact absurd ⟨z, h_has_corner⟩ h_corner
    · exact h_ends_down
    · exact absurd h_last_row hl
  choose q hq using h_down
  obtain rfl : half = fun z ↦ (q z).down := funext hq
  exact ⟨(l, l), ⟨l + 1, fun z ↦ (q z).right⟩, .diagonal q⟩

/-- Let a property of a path and a finite set of index pairs hold for the last path, through
`(m, m)`, and the empty set. Suppose that for each turn at `s` from `Γ` to `Γ'` and each set `T`
without `s`, it passes from `Γ'` and `T` to `Γ` and `insert s T`. Then it holds for the first path,
through `(0, 0)`, and the set of all `(i, j)` with `i, j < m`. -/
lemma turn_induction {motive : TwoGridPath m → Finset (ℕ × ℕ) → Prop} (h_last : motive (last m) ∅)
    (h_turn : ∀ (Γ : TwoGridPath m) (s : ℕ × ℕ) (Γ' : TwoGridPath m) (T : Finset (ℕ × ℕ)),
      Γ.Turn s Γ' → s ∉ T → motive Γ' T → motive Γ (insert s T)) :
    motive (first m) (range m ×ˢ range m) := by
  -- Induction on the number of squares between `Γ` and the last path.
  suffices h_above_path : ∀ (k : ℕ) (Γ : TwoGridPath m),
      #(range m ×ˢ range m \ Γ.squares) = k → motive Γ (range m ×ˢ range m \ Γ.squares) by
    simpa [squares_first] using h_above_path _ (first m) rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro Γ hk
    obtain rfl | h_ne := eq_or_ne Γ (last m)
    · simpa [squares_last] using h_last
    obtain ⟨s, Γ', hΓΓ' : Γ.Turn s Γ'⟩ := exists_turn h_ne
    obtain ⟨hs : s ∉ Γ.squares, h_eq : Γ'.squares = insert s Γ.squares⟩ := hΓΓ'.squares_eq
    have h_new : s ∉ range m ×ˢ range m \ Γ'.squares := by simp [h_eq]
    have h_above : range m ×ˢ range m \ Γ.squares =
        insert s (range m ×ˢ range m \ Γ'.squares) := by
      rw [h_eq, sdiff_insert, insert_erase (mem_sdiff.mpr ⟨hΓΓ'.mem_product, hs⟩)]
    rw [h_above] at hk ⊢
    exact h_turn Γ s Γ' _ hΓΓ' h_new (ih _ (by simp [← hk, h_new]) Γ' rfl)

end TwoGridPath

end New

end
