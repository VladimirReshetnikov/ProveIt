import Lib.Base

/-!
# A diagonal sweep of two monotone grid paths

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
* `New.TwoGridPath.sweep_induction`: move both halves along the same path. Each diagonal
  square contributes one turn and each pair of reflected off-diagonal squares contributes two.
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

/-- Extend a path by going straight down to level `k`. -/
def descend {k : ℕ} (p : GridPath a₀ b₀ a b) (hk : k ≤ b) : GridPath a₀ b₀ a k :=
  Nat.decreasingInduction (motive := fun k _ ↦ GridPath a₀ b₀ a k) (fun _ _ q ↦ q.down) p hk

@[simp] lemma descend_self (p : GridPath a₀ b₀ a b) : p.descend le_rfl = p := by simp [descend]

lemma descend_of_lt (p : GridPath a₀ b₀ a b) {k : ℕ} (hk : k < b) :
    p.descend hk.le = (p.descend hk).down :=
  Nat.decreasingInduction_succ_left _ _ hk _

private lemma descend_down (p : GridPath a₀ b₀ a (b + 1)) {k : ℕ} (hk : k ≤ b) :
    p.down.descend hk = p.descend (hk.trans b.le_succ) :=
  (Nat.decreasingInduction_succ (motive := fun k _ ↦ GridPath a₀ b₀ a k)
    (fun _ _ q ↦ q.down) p hk _).symm

private lemma append_descend_nil (p : GridPath a₀ b₀ a b) {k : ℕ} (hk : k ≤ b) :
    p.append ((nil : GridPath a b a b).descend hk) = p.descend hk := by
  induction hk using Nat.decreasingInduction with
  | self => simp [append]
  | of_succ k hk ih => simp only [descend_of_lt _ hk, append, ih]

/-- The path down the first column, from `(0, m)` to `(0, b)`. -/
def column (hb : b ≤ m) : GridPath 0 m 0 b := nil.descend hb

/-- The path along the row `m`, from `(0, m)` to `(a, m)`. -/
def row (m : ℕ) : ∀ a : ℕ, GridPath 0 m a m
  | 0 => nil
  | a + 1 => (row m a).right

lemma column_self : column (le_refl m) = nil := by
  exact descend_self nil

/-- The path down the first column from `(0, m)` to `(0, b)`, for `b < m`, is the one to
`(0, b + 1)` followed by a step down. -/
lemma column_of_lt (hb : b < m) : column hb.le = (column hb).down := by
  exact descend_of_lt nil hb

/-- Along a path from `(a₀, b₀)` to `(a, b)` the first index does not fall and the second does
not grow. -/
lemma le_and_le (p : GridPath a₀ b₀ a b) : a₀ ≤ a ∧ b ≤ b₀ := by
  induction p <;> omega

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

variable {m : ℕ}

/-- The first path, through `(0, 0)`: it goes left from `Ỹ^m_0` to `Ỹ^0_0` and up from `Y^0_0` to
`Y^0_m`, so both halves are recorded as going down the first column. -/
def first (m : ℕ) : TwoGridPath m := ⟨0, fun _ : Bool ↦ .column m.zero_le⟩

/-- The last path, through `(m, m)`: it goes up from `Ỹ^m_0` to `Ỹ^m_m` and left from `Y^m_m` to
`Y^0_m`, so both halves are recorded as going along the row `m`. -/
def last (m : ℕ) : TwoGridPath m := ⟨m, fun _ : Bool ↦ .row m m⟩

/-- Use the same path for the two reflected halves. -/
def double {j : ℕ} (p : GridPath 0 m j j) : TwoGridPath m := ⟨j, fun _ ↦ p⟩

/-- A path through the two grids meets the diagonal at an index at most `m`. -/
lemma diagonalIndex_le (Γ : TwoGridPath m) : Γ.diagonalIndex ≤ m := (Γ.half false).le_and_le.2

/-- Sweep the diagonal from 0 to `m`. After each diagonal turn, move its right step up to row
`m` in both halves. The index set records every square still to be crossed. -/
lemma sweep_induction {motive : TwoGridPath m → Finset (ℕ × ℕ) → Prop}
    (h_last : motive (last m) ∅)
    (h_diag : ∀ {j} (_ : j < m) (q : GridPath 0 m j (j + 1)) {T : Finset (ℕ × ℕ)},
      (j, j) ∉ T → motive (double q.right) T → motive (double q.down) (insert (j, j) T))
    (h_pair : ∀ {j b} (_ : j < b) (_ : b < m) (q : GridPath 0 m j (b + 1))
      (r : GridPath (j + 1) b (j + 1) (j + 1)) {T : Finset (ℕ × ℕ)},
      (j, b) ∉ T → (b, j) ∉ T → motive (double (q.right.down.append r)) T →
      motive (double (q.down.right.append r)) (insert (j, b) (insert (b, j) T))) :
    motive (first m) (range m ×ˢ range m) := by
  let square (j : ℕ) := Ico j m ×ˢ Ico j m
  -- After the diagonal turn, two reflected strips surround the remaining inner square.
  let strip (j b : ℕ) := square (j + 1) ∪ {j} ×ˢ Ico b m ∪ Ico b m ×ˢ {j}
  have stages (j : ℕ) (hj : j ≤ m) :
      motive (double ((GridPath.row m j).descend hj)) (square j) := by
    induction hj using Nat.decreasingInduction with
    | self => simpa [last, double, square] using h_last
    | of_succ j hj next =>
      -- At height `b`, slide the right step past one more down step in each half.
      have slide (b : ℕ) (hb : b ≤ m) (hjb : j + 1 ≤ b) :
          motive (double (((GridPath.row m j).descend hb).right.descend hjb)) (strip j b) := by
        induction hb using Nat.decreasingInduction with
        | self => simpa [strip, GridPath.row] using next
        | of_succ b hb ih =>
          let q := (GridPath.row m j).descend hb
          let r := (GridPath.nil : GridPath (j + 1) b (j + 1) b).descend hjb
          have hstep := h_pair hjb hb q r (T := strip j (b + 1))
            (by simp [strip, square]; omega) (by simp [strip, square]; omega)
          have heq : strip j b = insert (j, b) (insert (b, j) (strip j (b + 1))) := by
            ext ⟨x, y⟩; simp [strip, square]; omega
          rw [heq]
          simpa only [r, GridPath.append_descend_nil, GridPath.descend_down, q,
            ← GridPath.descend_of_lt _ hb] using hstep (by
              simpa only [r, GridPath.append_descend_nil, GridPath.descend_down] using ih (by omega))
      have heq : square j = insert (j, j) (strip j (j + 1)) := by
        ext ⟨x, y⟩; simp [strip, square]; omega
      rw [heq, GridPath.descend_of_lt _ hj]
      apply h_diag hj _ (by simp [strip, square])
      simpa only [GridPath.descend_self] using slide (j + 1) hj le_rfl
  simpa [first, double, GridPath.row, GridPath.column, square, Nat.Ico_zero_eq_range] using
    stages 0 (Nat.zero_le m)

end TwoGridPath

end New

end
