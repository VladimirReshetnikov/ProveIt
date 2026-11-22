import Std

/-! Algebraic step in contracting the two augmented incidence complexes.
    All theorems here are in the Lean host language. -/
namespace NerveCase

structure F2Group (C : Type) where
  zero : C
  add : C → C → C
  assoc : ∀ a b c, add (add a b) c = add a (add b c)
  comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  self : ∀ a, add a a = zero

namespace F2Group
variable {C : Type} (G : F2Group C)

theorem add_zero (a : C) : G.add a G.zero = a := by
  rw [G.comm, G.zero_add]

theorem cancel (a b : C) : G.add a (G.add a b) = b := by
  rw [← G.assoc, G.self, G.zero_add]

theorem shuffle (a b c d : C) :
    G.add (G.add a b) (G.add c d) = G.add (G.add a c) (G.add b d) := by
  rw [G.assoc, ← G.assoc b c d, G.comm b c, G.assoc c b d, ← G.assoc]

def residual (D h : C → C) (x : C) : C :=
  G.add x (G.add (D (h x)) (h (D x)))

theorem commute (D h : C → C)
    (dadd : ∀ x y, D (G.add x y) = G.add (D x) (D y))
    (dd : ∀ x, D (D x) = G.zero) (hz : h G.zero = G.zero) (x : C) :
    G.residual D h (D x) = D (G.residual D h x) := by
  simp only [residual, dadd, dd, hz, G.zero_add, G.add_zero]

def iterate (r : C → C) : Nat → C → C
  | 0, x => x
  | n+1, x => iterate r n (r x)

def repair (h r : C → C) : Nat → C → C
  | 0, _ => G.zero
  | n+1, x => G.add (h x) (repair h r n (r x))

theorem telescope (D h r : C → C)
    (dz : D G.zero = G.zero)
    (dadd : ∀ x y, D (G.add x y) = G.add (D x) (D y))
    (dcomm : ∀ x, r (D x) = D (r x))
    (defect : ∀ x, G.add (D (h x)) (h (D x)) = G.add x (r x)) (n : Nat) :
    ∀ x, G.add (D (G.repair h r n x)) (G.repair h r n (D x)) =
      G.add x (iterate r n x) := by
  induction n with
  | zero =>
    intro x
    simp only [repair, iterate, dz, G.self]
  | succ n ih =>
    intro x
    simp only [repair, iterate, dadd, dcomm]
    rw [G.shuffle, defect, ih, G.assoc, G.cancel]

theorem contraction (D h : C → C)
    (dz : D G.zero = G.zero)
    (dadd : ∀ x y, D (G.add x y) = G.add (D x) (D y))
    (dd : ∀ x, D (D x) = G.zero) (hz : h G.zero = G.zero)
    (N : Nat) (nilpotent : ∀ x, iterate (G.residual D h) N x = G.zero) (x : C) :
    let H := G.repair h (G.residual D h) N
    G.add (D (H x)) (H (D x)) = x := by
  dsimp only
  have defect (y : C) :
      G.add (D (h y)) (h (D y)) = G.add y (G.residual D h y) := by
    rw [residual, G.cancel]
  rw [G.telescope D h _ dz dadd (G.commute D h dadd dd hz) defect N x,
      nilpotent, G.add_zero]

theorem iterate_zero (r : C → C) (rz : r G.zero = G.zero) (n : Nat) :
    iterate r n G.zero = G.zero := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [iterate, rz] using ih

/-- For a chain in the cone, use the greatest opposite-coordinate degree
of a basis element in its support, assigning zero to the empty support. -/
theorem bounded_lowering [DecidableEq C] (r : C → C) (height : C → Nat)
    (rz : r G.zero = G.zero)
    (drops : ∀ x, r x ≠ G.zero → height (r x) < height x) (n : Nat) :
    ∀ x, height x < n → iterate r n x = G.zero := by
  induction n with
  | zero => intro x hx; omega
  | succ n ih =>
    intro x hx
    change iterate r n (r x) = G.zero
    by_cases kill : r x = G.zero
    · rw [kill, G.iterate_zero r rz]
    · have lower := drops x kill
      exact ih (r x) (by omega)

end F2Group

/-- Dot product of two positive rational vectors after assigning their
    coordinates common denominators (one per vector). -/
def dot (a b : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => dot a b n + a n * b n

theorem coordinate_le_dot (a b : Nat → Nat) (m : Nat) :
    ∀ i, i < m → a i * b i ≤ dot a b m := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    intro i hi
    simp only [dot]
    by_cases same : i = m
    · subst i; omega
    · have prev := ih i (by omega)
      omega

/-- One common coordinate with mass ≥ 1/m in each probability vector
    bounds the normalization denominator from below by 1/m². -/
theorem overlap_bound (a b : Nat → Nat) (m i da db : Nat) (hi : i < m)
    (ha : da ≤ m * a i) (hb : db ≤ m * b i) :
    da * db ≤ (m*m) * dot a b m := by
  calc
    da * db ≤ (m * a i) * (m * b i) := Nat.mul_le_mul ha hb
    _ = (m*m) * (a i * b i) := by ac_rfl
    _ ≤ (m*m) * dot a b m :=
      Nat.mul_le_mul_left _ (coordinate_le_dot a b m i hi)

end NerveCase

#print axioms NerveCase.F2Group.contraction
#print axioms NerveCase.F2Group.bounded_lowering
#print axioms NerveCase.overlap_bound
