import Std

/-!
# Selecting one row from each triangular matrix

This standalone file proves the finite algebra used in the row-selection
argument. Coordinates are indexed by `Fin n`. The determinant here is
defined for every square matrix by first-column cofactor expansion.
`Clears` uses actual finite row sums and an arbitrary integrality predicate.
-/

namespace FlagRows

open Lean.Grind

universe u
variable {R : Type u} [CommRing R]

abbrev Mat (R : Type u) (n : Nat) := Fin n → Fin n → R
abbrev Vec (R : Type u) (n : Nat) := Fin n → R

/-- Sum over all coordinates, in increasing order. -/
def sum : (n : Nat) → (Fin n → R) → R
  | 0, _ => 0
  | n + 1, f => f 0 + sum n (fun i => f i.succ)

/-- Product over all coordinates, in increasing order. -/
def prod : (n : Nat) → (Fin n → R) → R
  | 0, _ => 1
  | n + 1, f => f 0 * prod n (fun i => f i.succ)

theorem sum_zero_of_forall {n} (f : Fin n → R) (h : ∀ i, f i = 0) :
    sum n f = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change f 0 + sum n (fun i => f i.succ) = 0
    rw [h 0, ih (fun i => f i.succ) (fun i => h i.succ), Semiring.add_zero]

/-- Index in the original matrix corresponding to row `i` after deletion of `j`. -/
def skipRow {n : Nat} (j : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if i.val < j.val then i.castSucc else i.succ

/-- Delete row `j` and column zero. -/
def minor {n : Nat} (A : Mat R (n + 1)) (j : Fin (n + 1)) : Mat R n :=
  fun i k => A (skipRow j i) k.succ

/-- Laplace determinant, with cofactor sign `(-1)^j` in the first column. -/
def det : (n : Nat) → Mat R n → R
  | 0, _ => 1
  | n + 1, A => sum (n + 1) (fun j =>
      ((-1 : R)^j.val * A j 0) * det n (minor A j))

def Triangular {n} (A : Mat R n) : Prop :=
  ∀ i j : Fin n, j < i → A i j = 0

theorem triangular_det {n} (A : Mat R n) (h : Triangular A) :
    det n A = prod n (fun i => A i i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let M := minor A 0
    have hM (i j : Fin n) : M i j = A i.succ j.succ := by
      simp [M, minor, skipRow]
    have triM : Triangular M := by
      intro i j hj
      rw [hM]
      exact h _ _ (Fin.succ_lt_succ_iff.mpr hj)
    have diagM : (fun i => M i i) = (fun i : Fin n => A i.succ i.succ) :=
      funext (fun i => hM i i)
    have vanish : ∀ j : Fin n,
        ((-1 : R)^j.succ.val * A j.succ 0) * det n (minor A j.succ) = 0 := by
      intro j
      have h0 : (0 : Fin (n+1)) < j.succ := Nat.zero_lt_succ j.val
      rw [h j.succ 0 h0, Semiring.mul_zero, Semiring.zero_mul]
    change (((-1 : R)^0 * A 0 0) * det n M) +
        sum n (fun j => ((-1 : R)^j.succ.val * A j.succ 0) * det n (minor A j.succ)) =
        A 0 0 * prod n (fun i => A i.succ i.succ)
    rw [sum_zero_of_forall _ vanish, Semiring.add_zero, Semiring.pow_zero,
        Semiring.one_mul, ih M triM, diagM]

/-- Row `j` of the new matrix is row `j` of the original matrix `G j`. -/
def selectRows {n} (G : Fin n → Mat R n) : Mat R n :=
  fun j k => G j j k

def applyMatrix {n} (A : Mat R n) (x : Vec R n) : Vec R n :=
  fun j => sum n (fun k => A j k * x k)

/-- An arbitrary test set and an arbitrary predicate on scalar coordinates. -/
def Clears {n} (T : Vec R n → Prop) (integral : R → Prop) (A : Mat R n) : Prop :=
  ∀ x, T x → ∀ j, integral (applyMatrix A x j)

theorem selectRows_triangular {n} (G : Fin n → Mat R n) (h : ∀ i, Triangular (G i)) :
    Triangular (selectRows G) := fun i j hj => h i i j hj

theorem selectRows_apply {n} (G : Fin n → Mat R n) (x : Vec R n) (j : Fin n) :
    applyMatrix (selectRows G) x j = applyMatrix (G j) x j := rfl

/-- Each original matrix needs only to clear its own output coordinate. -/
theorem selectRows_clears_iff {n} (G : Fin n → Mat R n)
    (T : Vec R n → Prop) (integral : R → Prop) :
    Clears T integral (selectRows G) ↔
      ∀ x, T x → ∀ j, integral (applyMatrix (G j) x j) := Iff.rfl

/-- A simultaneous determinant identity and clearing statement, in all dimensions. -/
theorem selectRows_spec {n} (G : Fin n → Mat R n)
    (T : Vec R n → Prop) (integral : R → Prop)
    (hTri : ∀ i, Triangular (G i)) (hClear : ∀ i, Clears T integral (G i)) :
    Triangular (selectRows G) ∧
    det n (selectRows G) = prod n (fun i => G i i i) ∧
    Clears T integral (selectRows G) := by
  have h := selectRows_triangular G hTri
  exact ⟨h, triangular_det _ h, fun x hx j => hClear j x hx j⟩

end FlagRows

#print axioms FlagRows.selectRows_spec
