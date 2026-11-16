import Std

/-!
# The finite-column bound for an integral eigenvalue

Host-level integer arithmetic only. A caller supplies a maximizing coordinate
and its finite checks. The existence of such a coordinate is a bounded scan.
-/

namespace FiniteAlgebra

def dotColumn : List (Int × Int) → Int
  | [] => 0
  | (w, a) :: tail => w * a + dotColumn tail

def absoluteColumnSum : List (Int × Int) → Nat
  | [] => 0
  | (_, a) :: tail => a.natAbs + absoluteColumnSum tail

theorem dotColumn_bound (xs : List (Int × Int)) (W : Nat)
    (hW : ∀ p ∈ xs, p.1.natAbs ≤ W) :
    (dotColumn xs).natAbs ≤ W * absoluteColumnSum xs := by
  induction xs with
  | nil => simp [dotColumn, absoluteColumnSum]
  | cons p xs ih =>
      have hp := hW p (by simp)
      have ht : ∀ q ∈ xs, q.1.natAbs ≤ W := fun q hq => hW q (by simp [hq])
      have hi := ih ht
      simp only [dotColumn, absoluteColumnSum, Nat.mul_add]
      exact Nat.le_trans (Int.natAbs_add_le _ _)
        (Nat.add_le_add (by simpa [Int.natAbs_mul] using Nat.mul_le_mul_right p.2.natAbs hp) hi)

theorem integer_eigenvalue_bound (xs : List (Int × Int)) (lambda selected : Int)
    (W R : Nat) (hWpos : 0 < W) (hSelected : selected.natAbs = W)
    (hEntries : ∀ p ∈ xs, p.1.natAbs ≤ W)
    (hColumn : absoluteColumnSum xs ≤ R)
    (hEigen : dotColumn xs = lambda * selected) :
    lambda.natAbs ≤ R := by
  have hb := dotColumn_bound xs W hEntries
  rw [hEigen, Int.natAbs_mul, hSelected] at hb
  have hc := Nat.le_trans hb (Nat.mul_le_mul_left W hColumn)
  rw [Nat.mul_comm W R] at hc
  exact Nat.le_of_mul_le_mul_right hc hWpos

end FiniteAlgebra

#print axioms FiniteAlgebra.dotColumn_bound
#print axioms FiniteAlgebra.integer_eigenvalue_bound
