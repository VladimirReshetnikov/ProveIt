import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! The Fourier calculation used in the coprime-length construction. The two
row variables stand for one embedded root and the conjugate of a second one.
All identities are polynomial; a commutative domain suffices. -/

namespace FourierFrame

open Finset

variable {R : Type*} [CommRing R]

private lemma geom_blocks (w : R) (m p : ℕ) :
    (∑ j ∈ range m, w ^ j) * (∑ k ∈ range p, (w ^ m) ^ k) =
      ∑ l ∈ range (m * p), w ^ l := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [sum_range_succ, mul_add, ih, Nat.mul_succ, sum_range_add, sum_mul]
    congr 1
    apply sum_congr rfl
    intro j hj
    rw [← pow_mul, ← pow_add, Nat.add_comm]

private lemma geom_vanish [IsDomain R] {u : R} {p : ℕ}
    (hu : u ^ p = 1) (hu' : u ≠ 1) : ∑ k ∈ range p, u ^ k = 0 := by
  have h := geom_sum_mul u p
  rw [hu, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hu')

/-- Replace the constant column of a complete Fourier block by Gram weight
L. The identity includes the nonconstant columns and the outer modulation. -/
theorem corrected_gram [IsDomain R] (m p : ℕ) (hp : 0 < p)
    (x y A B A' B' L : R)
    (hx : (x ^ m) ^ p = 1) (hx' : x ^ m ≠ 1)
    (hy : (y ^ m) ^ p = 1) (hy' : y ^ m ≠ 1)
    (hL : L = (A+B)*(A'+B') - (p:R)*B*B') :
    (∑ j ∈ range m, (x*y)^j *
      ((∑ k ∈ (range p).erase 0,
        (A*(x^m)^k+B)*(A'*(y^m)^k+B')) + L)) =
      A*A' * ∑ l ∈ range (m*p), (x*y)^l := by
  let f (k : ℕ) := (A*(x^m)^k+B)*(A'*(y^m)^k+B')
  have hsum : ∑ k ∈ range p, f k =
      A*A' * (∑ k ∈ range p, ((x*y)^m)^k) + (p:R)*B*B' := by
    calc
      _ = ∑ k ∈ range p, (A*A' * ((x*y)^m)^k +
            A*B' * (x^m)^k + B*A' * (y^m)^k + B*B') := by
        apply sum_congr rfl
        intro k _
        simp only [f, mul_pow]
        ring
      _ = _ := by
        simp only [sum_add_distrib, ← mul_sum, geom_vanish hx hx',
          geom_vanish hy hy', mul_zero, add_zero, sum_const, card_range, nsmul_eq_mul]
        ring
  have hzero : 0 ∈ range p := mem_range.mpr hp
  have herase := sum_erase_add (s := range p) f hzero
  have h0 : f 0 = (A+B)*(A'+B') := by simp [f]
  have hinner : (∑ k ∈ (range p).erase 0, f k) + L =
      A*A' * ∑ k ∈ range p, ((x*y)^m)^k := by
    rw [hsum, h0] at herase
    rw [hL]
    linear_combination herase
  change (∑ j ∈ range m, (x*y)^j * ((∑ k ∈ (range p).erase 0, f k) + L)) = _
  simp only [hinner, ← sum_mul]
  rw [← geom_blocks]
  ring

/-- The full Gram entry is the requested scalar on equal rows and zero on
unequal rows. For character rows, x*y is the quotient of the embedded roots. -/
theorem geom_diagonal [IsDomain R] [DecidableEq R] (w : R) (n : ℕ) (hw : w ^ n = 1) :
    ∑ j ∈ range n, w ^ j = if w = 1 then (n:R) else 0 := by
  split_ifs with h
  · simp [h]
  · exact geom_vanish hw h

/-- Entry of the frame operator, including outer phase factors on both rows.
In a complex realization take y to be the conjugate of the second embedded
root, and A', B' to be the conjugates of A, B. -/
theorem frame_entry [IsDomain R] [DecidableEq R] (m p : ℕ) (hp : 0 < p)
    (x y A B A' B' L : R)
    (hx : (x ^ m) ^ p = 1) (hx' : x ^ m ≠ 1)
    (hy : (y ^ m) ^ p = 1) (hy' : y ^ m ≠ 1)
    (hL : L = (A+B)*(A'+B') - (p:R)*B*B') :
    (∑ j ∈ range m,
      ((∑ k ∈ (range p).erase 0,
        (x^j*(A*(x^m)^k+B))*(y^j*(A'*(y^m)^k+B'))) +
        L*x^j*y^j)) =
      if x*y = 1 then (m*p:R)*A*A' else 0 := by
  have hw : (x*y) ^ (m*p) = 1 := by
    rw [mul_pow, pow_mul, pow_mul, hx, hy, one_mul]
  calc
    _ = ∑ j ∈ range m, (x*y)^j *
        ((∑ k ∈ (range p).erase 0, (A*(x^m)^k+B)*(A'*(y^m)^k+B')) + L) := by
      apply sum_congr rfl
      intro j _
      rw [mul_add, mul_sum, mul_pow]
      congr 1
      · apply sum_congr rfl
        intro k _
        ring
      · ring
    _ = _ := by
      rw [corrected_gram m p hp x y A B A' B' L hx hx' hy hy' hL, geom_diagonal _ _ hw]
      split_ifs <;> push_cast <;> ring

end FourierFrame

#print axioms FourierFrame.corrected_gram
#print axioms FourierFrame.geom_diagonal
#print axioms FourierFrame.frame_entry
