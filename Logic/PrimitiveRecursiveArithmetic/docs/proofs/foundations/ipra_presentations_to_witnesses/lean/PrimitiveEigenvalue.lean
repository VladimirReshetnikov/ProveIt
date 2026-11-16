import Std

/-!
# An exact denominator certificate for a rational eigenvalue

These are host-level Lean theorems over explicit finite integer data. They are
not, by themselves, object `Prf PRAAx` derivations. The input `z` is the integral
matrix product. The matrix need not be stored again once those equations have
been checked. The primitive vector is certified by a finite Bezout identity.
-/

namespace FiniteAlgebra

structure Coordinate where
  coefficient : Int
  vector : Int
  image : Int

def vectorSum : List Coordinate → Int
  | [] => 0
  | x :: xs => x.coefficient * x.vector + vectorSum xs

def imageSum : List Coordinate → Int
  | [] => 0
  | x :: xs => x.coefficient * x.image + imageSum xs

def EigenEquation (a b : Int) (xs : List Coordinate) : Prop :=
  ∀ x ∈ xs, b * x.image = a * x.vector

theorem weighted_eigen_equation (a b : Int) (xs : List Coordinate)
    (h : EigenEquation a b xs) :
    b * imageSum xs = a * vectorSum xs := by
  induction xs with
  | nil => simp [vectorSum, imageSum]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht : EigenEquation a b xs := fun y hy => h y (by simp [hy])
      have hi := ih ht
      simp only [vectorSum, imageSum]
      calc
        b * (x.coefficient * x.image + imageSum xs) =
            x.coefficient * (b * x.image) + b * imageSum xs := by
          simp only [Int.mul_add, Int.mul_left_comm]
        _ = x.coefficient * (a * x.vector) + a * vectorSum xs := by rw [hx, hi]
        _ = a * (x.coefficient * x.vector + vectorSum xs) := by
          simp only [Int.mul_add, Int.mul_left_comm]

theorem denominator_divides_numerator (a b : Int) (xs : List Coordinate)
    (h : EigenEquation a b xs) (primitive : vectorSum xs = 1) :
    b ∣ a := by
  refine ⟨imageSum xs, ?_⟩
  have he := weighted_eigen_equation a b xs h
  rw [primitive, Int.mul_one] at he
  exact he.symm

/-- A positive reduced denominator of an integral matrix's rational eigenvalue
is 1. `u*a+v*b=1` witnesses reducedness; `vectorSum xs=1` witnesses primitivity.
The conclusion follows by finite integer algebra, without characteristic
polynomials or Cayley--Hamilton. -/
theorem reduced_denominator_eq_one (a b u v : Int) (xs : List Coordinate)
    (hb : 0 < b) (reduced : u * a + v * b = 1)
    (primitive : vectorSum xs = 1) (eigen : EigenEquation a b xs) :
    b = 1 := by
  obtain ⟨k, hk⟩ := denominator_divides_numerator a b xs eigen primitive
  apply Int.eq_one_of_dvd_one (by omega)
  refine ⟨u * k + v, ?_⟩
  rw [hk] at reduced
  calc
    1 = u * (b * k) + v * b := reduced.symm
    _ = b * (u * k + v) := by
      rw [Int.mul_add, Int.mul_left_comm u b k, Int.mul_comm v b]

/-- A fully reduced kernel example: matrix [2], eigenvalue 2/1, vector [1]. -/
def exampleData : List Coordinate := [{coefficient := 1, vector := 1, image := 2}]

example : EigenEquation 2 1 exampleData := by
  intro x hx
  simp [exampleData] at hx
  subst x
  decide

end FiniteAlgebra

#print axioms FiniteAlgebra.weighted_eigen_equation
#print axioms FiniteAlgebra.reduced_denominator_eq_one
