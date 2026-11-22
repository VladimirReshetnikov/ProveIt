import Std

/-!
Finite, effective operations used to observe the oloid surface distance.
All searches are bounded. The cost functions in the mesh theorems are
parameters: the analytic estimates for the particular oloid supply the
hypotheses. No real numbers, extrema on continua, or choice are used.
-/
namespace Oloid.Finite

/-- Least index tie convention for a minimum on [0,n]. -/
def best (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 =>
    let j := best f n
    if f (n+1) < f j then n+1 else j

theorem best_spec (f : Nat → Nat) (n : Nat) :
    best f n ≤ n ∧ ∀ i, i ≤ n → f (best f n) ≤ f i := by
  induction n with
  | zero =>
    constructor
    · exact Nat.le_refl _
    · intro i hi
      have : i = 0 := by omega
      subst i
      exact Nat.le_refl _
  | succ n ih =>
    obtain ⟨hb, hmin⟩ := ih
    unfold best
    simp only
    split
    · rename_i h
      constructor
      · exact Nat.le_refl _
      · intro i hi
        by_cases h' : i ≤ n
        · exact Nat.le_trans (Nat.le_of_lt h) (hmin i h')
        · have : i = n+1 := by omega
          subst i
          exact Nat.le_refl _
    · rename_i h
      constructor
      · omega
      · intro i hi
        by_cases h' : i ≤ n
        · exact hmin i h'
        · have : i = n+1 := by omega
          subst i
          omega

def minCost (f : Nat → Nat) (n : Nat) := f (best f n)

/-- Minimize a two-contact word (one contact can be a dummy).
Both coordinates range over all n+1 grid vertices, independently. -/
def meshCost (f : Nat → Nat → Nat) (n : Nat) :=
  minCost (fun i => minCost (f i) n) n

theorem mesh_le (f : Nat → Nat → Nat) (n i j : Nat)
    (hi : i ≤ n) (hj : j ≤ n) : meshCost f n ≤ f i j :=
  Nat.le_trans ((best_spec (fun k => minCost (f k) n) n).2 i hi)
    ((best_spec (f i) n).2 j hj)

theorem mesh_attains (f : Nat → Nat → Nat) (n : Nat) :
    ∃ i ≤ n, ∃ j ≤ n, meshCost f n = f i j := by
  let i := best (fun k => minCost (f k) n) n
  exact ⟨i, (best_spec _ _).1, best (f i) n, (best_spec _ _).1, rfl⟩

/-- Integer costs of two meshes expressed in a common unit. A rounding
map sends every fine contact pair to a feasible coarse contact pair. -/
theorem rounding_bound (f g : Nat → Nat → Nat) (n m E : Nat)
    (round : Nat → Nat) (bounded : ∀ i, i ≤ m → round i ≤ n)
    (cost : ∀ i ≤ m, ∀ j ≤ m, f (round i) (round j) ≤ g i j + E) :
    meshCost f n ≤ meshCost g m + E := by
  obtain ⟨i, hi, j, hj, e⟩ := mesh_attains g m
  rw [e]
  exact Nat.le_trans (mesh_le f n _ _ (bounded i hi) (bounded j hj)) (cost i hi j hj)

/-- Two-sided comparison from explicit maps and errors, e.g. dyadic
embedding in one direction and truncation of extra bits in the other. -/
theorem mesh_stability (f g : Nat → Nat → Nat) (n m E : Nat)
    (down up : Nat → Nat)
    (bd : ∀ i, i ≤ m → down i ≤ n) (bu : ∀ i, i ≤ n → up i ≤ m)
    (hd : ∀ i ≤ m, ∀ j ≤ m, f (down i) (down j) ≤ g i j + E)
    (hu : ∀ i ≤ n, ∀ j ≤ n, g (up i) (up j) ≤ f i j + E) :
    meshCost f n ≤ meshCost g m + E ∧ meshCost g m ≤ meshCost f n + E :=
  ⟨rounding_bound _ _ _ _ _ down bd hd, rounding_bound _ _ _ _ _ up bu hu⟩

/-- A rational parameter. Directed comparisons use cross multiplication. -/
structure Param where
  num : Nat
  den : Nat
  positive : 0 < den

structure Box where
  xlo : Nat
  xhi : Nat
  ylo : Nat
  yhi : Nat

/-- Bounds are integers in units 1/unit; p and q need not be dyadic. -/
def inside (b : Box) (unit : Nat) (p q : Param) : Prop :=
  b.xlo * p.den ≤ p.num * unit ∧ p.num * unit ≤ b.xhi * p.den ∧
  b.ylo * q.den ≤ q.num * unit ∧ q.num * unit ≤ b.yhi * q.den

inductive Tree where
  | leaf (id : Nat)
  | splitX (mid : Nat) (left right : Tree)
  | splitY (mid : Nat) (left right : Tree)

/-- Each leaf checks a local certificate. The split automatically passes
the inherited edge coordinates into the two child boxes. -/
def check (leaf : Nat → Box → Bool) : Tree → Box → Bool
  | .leaf id, b => leaf id b
  | .splitX m l r, b =>
    check leaf l {b with xhi := m} && check leaf r {b with xlo := m}
  | .splitY m l r, b =>
    check leaf l {b with yhi := m} && check leaf r {b with ylo := m}

/-- Coverage at arbitrary rational parameters. The assertion carried by a
leaf can be a lower bound, or the disjunction used to isolate a minimizer. -/
theorem check_sound (test : Nat → Box → Bool) (unit : Nat) (P : Param → Param → Prop)
    (valid : ∀ id b p q, test id b = true → inside b unit p q → P p q)
    (t : Tree) (b : Box) (accepted : check test t b = true)
    (p q : Param) (hit : inside b unit p q) : P p q := by
  induction t generalizing b with
  | leaf id => exact valid id b p q accepted hit
  | splitX m l r hl hr =>
    obtain ⟨lo, hi, lo', hi'⟩ := hit
    obtain ⟨al, ar⟩ := Bool.and_eq_true_iff.mp accepted
    by_cases h : p.num * unit ≤ m * p.den
    · exact hl _ al ⟨lo, h, lo', hi'⟩
    · exact hr _ ar ⟨Nat.le_of_lt (Nat.lt_of_not_ge h), hi, lo', hi'⟩
  | splitY m l r hl hr =>
    obtain ⟨lo, hi, lo', hi'⟩ := hit
    obtain ⟨al, ar⟩ := Bool.and_eq_true_iff.mp accepted
    by_cases h : q.num * unit ≤ m * q.den
    · exact hl _ al ⟨lo, hi, lo', h⟩
    · exact hr _ ar ⟨lo, hi, Nat.le_of_lt (Nat.lt_of_not_ge h), hi'⟩

end Oloid.Finite
