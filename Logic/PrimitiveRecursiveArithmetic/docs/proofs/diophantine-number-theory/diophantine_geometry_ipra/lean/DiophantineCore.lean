import Std

/-!
# Arithmetic core for constructive Diophantine geometry

This file contains ordinary Lean theorems. It is not an embedded derivation
in iPRA. The accompanying roadmap explains the remaining syntactic work.
Only Lean's bundled Std is imported; Mathlib is not needed.

The geometric identities are stated over integers after clearing
denominators. The search and descent functions recurse on explicit fuel.
-/

namespace DiophantineIPRA

/- Expand integer polynomials using constructive ring laws; `omega`
then checks an integer linear identity between canonical monomials.
No classical ring-normalization theorem is invoked. -/
set_option linter.unusedSimpArgs false in
macro "integer_polynomial" : tactic => `(tactic|
  ((try simp only [Int.pow_succ, Int.pow_zero, Int.mul_one, Int.one_mul,
      Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
      Int.mul_neg, Int.neg_mul, Int.neg_neg,
      Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]) <;>
   (try simp only [Int.reduceMul]) <;>
   (try simp only [← Int.mul_assoc]) <;>
   omega))


/-! ## Bounded Boolean search -/

/-- Test the closed initial interval `{0, ..., n}`. -/
def anyLE (p : Nat → Bool) : Nat → Bool
  | 0 => p 0
  | n + 1 => anyLE p n || p (n + 1)

theorem anyLE_correct (p : Nat → Bool) (n : Nat) :
    anyLE p n = true ↔ ∃ k, k ≤ n ∧ p k = true := by
  induction n with
  | zero => simp [anyLE]
  | succ n ih =>
    simp only [anyLE, Bool.or_eq_true, ih]
    constructor
    · intro h
      cases h with
      | inl h =>
        obtain ⟨k, hk, hp⟩ := h
        exact ⟨k, Nat.le_trans hk (Nat.le_succ n), hp⟩
      | inr h => exact ⟨n + 1, Nat.le_refl _, h⟩
    · intro h
      obtain ⟨k, hk, hp⟩ := h
      by_cases hkn : k ≤ n
      · exact Or.inl ⟨k, hkn, hp⟩
      · have heq : k = n + 1 := by omega
        exact Or.inr (heq ▸ hp)

/-- The executable witness search returns the least successful index. -/
def findLE (p : Nat → Bool) : Nat → Option Nat
  | 0 => if p 0 then some 0 else none
  | n + 1 =>
    match findLE p n with
    | some k => some k
    | none => if p (n + 1) then some (n + 1) else none

theorem findLE_sound (p : Nat → Bool) (n k : Nat)
    (h : findLE p n = some k) : k ≤ n ∧ p k = true := by
  induction n with
  | zero =>
    simp only [findLE] at h
    split at h
    · simp_all
    · contradiction
  | succ n ih =>
    simp only [findLE] at h
    split at h
    next j hj =>
      have hjk : j = k := Option.some.inj h
      subst j
      have hk := ih hj
      exact ⟨Nat.le_trans hk.1 (Nat.le_succ n), hk.2⟩
    next hn =>
      split at h
      next hp =>
        have hnk : n + 1 = k := Option.some.inj h
        subst k
        exact ⟨Nat.le_refl _, hp⟩
      next => contradiction

theorem findLE_none_iff (p : Nat → Bool) (n : Nat) :
    findLE p n = none ↔ anyLE p n = false := by
  induction n with
  | zero => simp [findLE, anyLE]
  | succ n ih =>
    simp only [findLE, anyLE]
    cases hfind : findLE p n with
    | none =>
      have hfalse : anyLE p n = false := ih.mp hfind
      simp [hfalse]
    | some k =>
      have htrue : anyLE p n = true :=
        (anyLE_correct p n).mpr ⟨k, findLE_sound p n k hfind⟩
      simp [htrue]

/-! ## Explicit finite descent -/

/-- Iteration with the number of steps displayed as a natural argument. -/
def run (step : Nat → Nat) (start : Nat) : Nat → Nat
  | 0 => start
  | k + 1 => step (run step start k)

/-- A Boolean condition cannot persist while a natural rank strictly falls.
The contradiction is reached after `rank start + 1` iterations. -/
theorem noBooleanDescent (good : Nat → Bool) (step rank : Nat → Nat)
    (decrease : ∀ s, good s = true →
      good (step s) = true ∧ rank (step s) < rank s)
    (start : Nat) : good start ≠ true := by
  intro hstart
  have invariant (k : Nat) :
      good (run step start k) = true ∧
      rank (run step start k) + k ≤ rank start := by
    induction k with
    | zero => exact ⟨hstart, Nat.le_refl _⟩
    | succ k ih =>
      have hs := decrease (run step start k) ih.1
      constructor
      · exact hs.1
      · simp only [run]
        omega
  have impossible := (invariant (rank start + 1)).2
  omega

/-! ## Homogeneous quadratic geometry -/

structure Vec3 where
  x : Int
  y : Int
  z : Int
  deriving DecidableEq, Repr

structure Quad3 where
  a : Int
  b : Int
  c : Int
  d : Int
  e : Int
  f : Int
  deriving DecidableEq, Repr

def qeval (q : Quad3) (p : Vec3) : Int :=
  q.a * p.x ^ 2 + q.b * p.y ^ 2 + q.c * p.z ^ 2 +
  q.d * p.x * p.y + q.e * p.x * p.z + q.f * p.y * p.z

def polar (q : Quad3) (p r : Vec3) : Int :=
  2 * q.a * p.x * r.x + 2 * q.b * p.y * r.y + 2 * q.c * p.z * r.z +
  q.d * (p.x * r.y + p.y * r.x) +
  q.e * (p.x * r.z + p.z * r.x) +
  q.f * (p.y * r.z + p.z * r.y)

def lincomb (a b : Int) (p r : Vec3) : Vec3 :=
  ⟨a * p.x + b * r.x, a * p.y + b * r.y, a * p.z + b * r.z⟩

theorem quadratic_expansion (q : Quad3) (p r : Vec3) (a b : Int) :
    qeval q (lincomb a b p r) =
      a ^ 2 * qeval q p + a * b * polar q p r + b ^ 2 * qeval q r := by
  simp only [qeval, lincomb, polar]
  integer_polynomial

/-- The second intersection numerator, before projective normalization. -/
def second (q : Quad3) (p r : Vec3) : Vec3 :=
  lincomb (qeval q r) (-polar q p r) p r

theorem second_identity (q : Quad3) (p r : Vec3) :
    qeval q (second q p r) = qeval q r ^ 2 * qeval q p := by
  simp only [second, quadratic_expansion]
  integer_polynomial

theorem second_on_conic (q : Quad3) (p r : Vec3)
    (hp : qeval q p = 0) : qeval q (second q p r) = 0 := by
  rw [second_identity, hp]
  simp

/-! ## Circle and congruent-number formulas -/

theorem circle_identity (u v : Int) :
    (u ^ 2 - v ^ 2) ^ 2 + (2 * u * v) ^ 2 = (u ^ 2 + v ^ 2) ^ 2 := by
  integer_polynomial

theorem circle_inverse_identity (u v : Int) :
    (2 * u * v) * u = ((u ^ 2 + v ^ 2) + (u ^ 2 - v ^ 2)) * v := by
  integer_polynomial

theorem elliptic_triangle_identity (x n : Int) :
    (x ^ 2 - n ^ 2) ^ 2 + (2 * n * x) ^ 2 = (x ^ 2 + n ^ 2) ^ 2 := by
  integer_polynomial

theorem elliptic_triangle_area (x y n : Int)
    (h : y ^ 2 = x ^ 3 - n ^ 2 * x) :
    (x ^ 2 - n ^ 2) * (2 * n * x) = 2 * n * y ^ 2 := by
  rw [h]
  integer_polynomial

/-- Polynomial certificate for the reverse triangle-to-curve formula. -/
theorem triangle_curve_certificate (a b c n : Int) :
    (2 * n ^ 2 * (a + c)) ^ 2 * b ^ 2 -
      ((n * (a + c) * b) ^ 3 -
        n ^ 2 * (n * (a + c) * b) * (b ^ 2) ^ 2) =
    2 * n ^ 3 * (a + c) ^ 2 * b ^ 2 * (2 * n - a * b) +
      n ^ 3 * (a + c) * b ^ 3 * (a ^ 2 + b ^ 2 - c ^ 2) := by
  integer_polynomial

theorem triangle_on_curve (a b c n : Int)
    (htri : a ^ 2 + b ^ 2 = c ^ 2) (harea : a * b = 2 * n) :
    (2 * n ^ 2 * (a + c)) ^ 2 * b ^ 2 =
      (n * (a + c) * b) ^ 3 -
        n ^ 2 * (n * (a + c) * b) * (b ^ 2) ^ 2 := by
  have cert := triangle_curve_certificate a b c n
  rw [htri, harea] at cert
  simp only [Int.sub_self, Int.mul_zero, Int.add_zero] at cert
  omega

end DiophantineIPRA

#print axioms DiophantineIPRA.anyLE_correct
#print axioms DiophantineIPRA.findLE_sound
#print axioms DiophantineIPRA.findLE_none_iff
#print axioms DiophantineIPRA.noBooleanDescent
#print axioms DiophantineIPRA.quadratic_expansion
#print axioms DiophantineIPRA.second_identity
#print axioms DiophantineIPRA.second_on_conic
#print axioms DiophantineIPRA.circle_identity
#print axioms DiophantineIPRA.circle_inverse_identity
#print axioms DiophantineIPRA.elliptic_triangle_identity
#print axioms DiophantineIPRA.elliptic_triangle_area
#print axioms DiophantineIPRA.triangle_curve_certificate
#print axioms DiophantineIPRA.triangle_on_curve
