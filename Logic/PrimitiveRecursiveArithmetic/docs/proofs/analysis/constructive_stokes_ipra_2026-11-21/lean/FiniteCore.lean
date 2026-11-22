import Std

/-!
# Finite algebra used by constructive Stokes

Status: proof scripts supplied, but NOT compiled in the delivery environment.
This file uses only the Lean standard library, not Mathlib.  It is an ambient
Lean model of the finite arithmetic identities.  It is NOT a derivation of the
analytic theorem in object-level iPRA.  See `StokesBlueprint.lean.txt` and the
repository integration plan for that separate task.

All sums below are primitive recursions.  Integer-valued functions model
rational samples after multiplication by a common positive denominator.
The two inequalities in `line_estimate` encode an absolute-value bound without
using real numbers, limits, or a choice operator.
-/

namespace ConstructiveStokes

/-- Primitive-recursive finite sum, with the upper endpoint excluded. -/
def isum : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => isum n f + f n

@[simp] theorem isum_zero (f : Nat → Int) : isum 0 f = 0 := rfl

@[simp] theorem isum_succ (n : Nat) (f : Nat → Int) :
    isum (n + 1) f = isum n f + f n := rfl

/-- Exact finite FTC.  No convergence assertion occurs here. -/
theorem telescope (f : Nat → Int) (n : Nat) :
    isum n (fun j => f (j + 1) - f j) = f n - f 0 := by
  induction n with
  | zero => simp [isum]
  | succ n ih =>
      simp only [isum]
      omega

theorem isum_add (f g : Nat → Int) (n : Nat) :
    isum n (fun j => f j + g j) = isum n f + isum n g := by
  induction n with
  | zero => simp [isum]
  | succ n ih =>
      simp only [isum]
      omega

theorem isum_sub (f g : Nat → Int) (n : Nat) :
    isum n (fun j => f j - g j) = isum n f - isum n g := by
  induction n with
  | zero => simp [isum]
  | succ n ih =>
      simp only [isum]
      omega

theorem isum_mono (f g : Nat → Int) :
    ∀ n, (∀ j, j < n → f j ≤ g j) → isum n f ≤ isum n g := by
  intro n
  induction n with
  | zero =>
      intro h
      simp [isum]
  | succ n ih =>
      intro h
      have hprev : isum n f ≤ isum n g := ih (by
        intro j hj
        exact h j (Nat.lt_trans hj (Nat.lt_succ_self n)))
      have hlast : f n ≤ g n := h n (Nat.lt_succ_self n)
      simp only [isum]
      omega

theorem isum_congr (f g : Nat → Int) :
    ∀ n, (∀ j, j < n → f j = g j) → isum n f = isum n g := by
  intro n
  induction n with
  | zero =>
      intro h
      rfl
  | succ n ih =>
      intro h
      have hprev : isum n f = isum n g := ih (by
        intro j hj
        exact h j (Nat.lt_trans hj (Nat.lt_succ_self n)))
      have hlast : f n = g n := h n (Nat.lt_succ_self n)
      simp only [isum, hprev, hlast]

/-- An error may vary from cell to cell.  Uniform errors are a specialization. -/
theorem line_upper (g f e : Nat → Int) (n : Nat)
    (h : ∀ j, j < n → g (j + 1) - g j - f j ≤ e j) :
    g n - g 0 - isum n f ≤ isum n e := by
  have hm := isum_mono (fun j => g (j + 1) - g j - f j) e n h
  have hs := isum_sub (fun j => g (j + 1) - g j) f n
  have ht := telescope g n
  omega

theorem line_lower (g f e : Nat → Int) (n : Nat)
    (h : ∀ j, j < n → f j - (g (j + 1) - g j) ≤ e j) :
    isum n f - (g n - g 0) ≤ isum n e := by
  have hm := isum_mono (fun j => f j - (g (j + 1) - g j)) e n h
  have hs := isum_sub f (fun j => g (j + 1) - g j) n
  have ht := telescope g n
  omega

/-- A pair of signed inequalities is the rational absolute-error contract. -/
theorem line_estimate (g f e : Nat → Int) (n : Nat)
    (hu : ∀ j, j < n → g (j + 1) - g j - f j ≤ e j)
    (hl : ∀ j, j < n → f j - (g (j + 1) - g j) ≤ e j) :
    (g n - g 0 - isum n f ≤ isum n e) ∧
    (isum n f - (g n - g 0) ≤ isum n e) :=
  ⟨line_upper g f e n hu, line_lower g f e n hl⟩

/-- Sum over all transverse grid rows for one coordinate direction. -/
def rowBulk : List (Nat → Int) → Nat → Int
  | [], _ => 0
  | f :: fs, n => isum n (fun j => f (j + 1) - f j) + rowBulk fs n

/-- The two opposite boundary faces for those same rows. -/
def rowBoundary : List (Nat → Int) → Nat → Int
  | [], _ => 0
  | f :: fs, n => (f n - f 0) + rowBoundary fs n

/-- Exact cubical cancellation in one direction, before quadrature errors. -/
theorem rows_stokes (rows : List (Nat → Int)) (n : Nat) :
    rowBulk rows n = rowBoundary rows n := by
  induction rows with
  | nil => rfl
  | cons f fs ih =>
      simp only [rowBulk, rowBoundary, telescope, ih]

/-- The oriented boundary of a square, evaluated once more on its vertices. -/
def boundaryBoundarySquare (v : Bool → Bool → Int) : Int :=
  (v true true - v true false) -
  (v false true - v false false) -
  (v true true - v false true) +
  (v true false - v false false)

theorem boundary_squared_square (v : Bool → Bool → Int) :
    boundaryBoundarySquare v = 0 := by
  unfold boundaryBoundarySquare
  omega

/-- Paired interior faces disappear with opposite orientations. -/
theorem opposite_faces_cancel (a b : Int) : a + b - b = a := by
  omega

end ConstructiveStokes
