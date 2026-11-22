import IntervalLift

namespace BudgetAnalysis.CellGeometry
open IntervalLift (UnitQ eps)

def cells (n : Nat) : Nat := 2^n

/-- The endpoint 1 belongs to the last cell, with index 2^n - 1. -/
def index (n : Nat) (x : UnitQ) : Nat :=
  min (cells n - 1) (((cells n : ℚ) * x.val).floor.toNat)

theorem index_lt (n : Nat) (x : UnitQ) : index n x < cells n := by
  have positive : 0 < cells n := Nat.two_pow_pos _
  have bound : index n x ≤ cells n - 1 := Nat.min_le_left .. 
  omega

theorem width_identity (n : Nat) : (cells n : ℚ) * eps n = 1 := by
  simp only [cells, eps, Nat.cast_pow, Nat.cast_ofNat, ← mul_pow]
  norm_num

theorem index_neighbours (n : Nat) (x y : UnitQ) (order : x.val ≤ y.val)
    (width : y.val - x.val ≤ eps n) :
    index n y = index n x ∨ index n y = index n x + 1 := by
  let K : ℚ := cells n
  have nonneg : 0 ≤ K := Nat.cast_nonneg _
  have a : (K*x.val).floor ≤ (K*y.val).floor :=
    Rat.floor_monotone (mul_le_mul_of_nonneg_left order nonneg)
  have rel : K * (y.val-x.val) ≤ 1 :=
    (mul_le_mul_of_nonneg_left width nonneg).trans_eq (width_identity n)
  rw [mul_sub] at rel
  have b : (K*y.val).floor ≤ (K*x.val).floor + 1 := by
    rw [← Rat.floor_add_one]
    exact Rat.floor_monotone (by linarith)
  change min _ (K*y.val).floor.toNat = min _ (K*x.val).floor.toNat ∨
    min _ (K*y.val).floor.toNat = min _ (K*x.val).floor.toNat + 1
  omega

/-- Endpoint evidence supplies a value seen from each side of an interior
boundary. The functions L and R are indexed by the cell to its left. -/
structure CellData (n : Nat) (eta e : ℚ) where
  V : UnitQ → ℚ
  L : Nat → ℚ
  R : Nat → ℚ
  same : ∀ x y, index n x = index n y → |V x - V y| ≤ eta
  fromLeft : ∀ x i, index n x = i → i+1 < cells n → |V x - L i| ≤ eta
  fromRight : ∀ y i, index n y = i+1 → |R i - V y| ≤ eta
  glued : ∀ i, i+1 < cells n → |L i - R i| ≤ 2*e

theorem adjacent_ordered {n : Nat} {eta e : ℚ} (C : CellData n eta e)
    (pos : 0 ≤ eta) (err : 0 ≤ e) (x y : UnitQ) (xy : x.val ≤ y.val)
    (close : y.val - x.val ≤ eps n) : |C.V x - C.V y| ≤ 2*eta + 2*e := by
  rcases index_neighbours n x y xy close with same | next
  · linarith [C.same x y same.symm]
  · let i := index n x
    have inside : i+1 < cells n := next ▸ index_lt n y
    have left := C.fromLeft x i rfl inside
    have right := C.fromRight y i next
    have glue := C.glued i inside
    linarith [abs_sub_le (C.V x) (C.L i) (C.V y),
      abs_sub_le (C.L i) (C.R i) (C.V y)]

theorem adjacent {n : Nat} {eta e : ℚ} (C : CellData n eta e)
    (pos : 0 ≤ eta) (err : 0 ≤ e) (x y : UnitQ)
    (close : |x.val - y.val| ≤ eps n) : |C.V x - C.V y| ≤ 2*eta + 2*e := by
  rcases le_total x.val y.val with xy | yx
  · apply adjacent_ordered C pos err x y xy
    linarith [(abs_le.mp close).1]
  · rw [abs_sub_comm]
    exact adjacent_ordered C pos err y x yx (abs_le.mp close).2

/-- An exact-prefix table has eta=0. Its adjacent-cell estimate supplies the
hypothesis of the numerical Cauchy-name lifting theorem. -/
def observation (N : Nat → Nat) (C : ∀ k, CellData (N k) 0 (eps k))
    (cons : ∀ k l x, |(C k).V x - (C l).V x| ≤ eps k + eps l) :
    IntervalLift.Observation where
  V k := (C k).V
  N := N
  consistent := cons
  adjacent k x y h := by
    simpa using adjacent (C k) (le_refl 0) (IntervalLift.eps_nonneg k) x y h

end BudgetAnalysis.CellGeometry
