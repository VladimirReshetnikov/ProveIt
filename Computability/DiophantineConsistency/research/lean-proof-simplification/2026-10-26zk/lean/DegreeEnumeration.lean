import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace NewDegreeEnumeration
open scoped BigOperators

/-- An executable list, with neither a classical choice nor a Cartesian filter. -/
def degreeVectors (n d : ℕ) : List (Fin n → ℕ) :=
  List.Nat.antidiagonalTuple n d

/-- This is the precise finite set used by Jones1982.star. -/
theorem vectors_toFinset (n d : ℕ) :
    (degreeVectors n d).toFinset =
      (Finset.univ : Finset (Fin n)).piAntidiag d := by
  ext k
  simp [degreeVectors, List.Nat.mem_antidiagonalTuple, Finset.mem_piAntidiag]

/-- Any additive evaluator can use the constructive enumeration. -/
theorem sum_vectors {M : Type*} [AddCommMonoid M] (n d : ℕ)
    (f : (Fin n → ℕ) → M) :
    ((degreeVectors n d).map f).sum =
      ∑ k ∈ (Finset.univ : Finset (Fin n)).piAntidiag d, f k := by
  calc
    _ = (degreeVectors n d).toFinset.sum f :=
      (List.sum_toFinset f (show (degreeVectors n d).Nodup from
        List.Nat.nodup_antidiagonalTuple n d)).symm
    _ = _ := by rw [vectors_toFinset]

/-- A generic form of the exact `sumExpressions` evaluation adapter. -/
theorem eval_sum_vectors {S M : Type*} [AddCommMonoid M]
    (eval : S → M) (sumSyntax : List S → S)
    (heval : ∀ es, eval (sumSyntax es) = (es.map eval).sum)
    (n d : ℕ) (f : (Fin n → ℕ) → S) :
    eval (sumSyntax ((degreeVectors n d).map f)) =
      ∑ k ∈ (Finset.univ : Finset (Fin n)).piAntidiag d, eval (f k) := by
  rw [heval, List.map_map]
  exact sum_vectors n d (fun k => eval (f k))

/-- Small kernel-reduced cardinality controls, including the degree-zero corner. -/
example : (degreeVectors 2 4).length = 5 := by decide
example : (degreeVectors 4 4).length = 35 := by decide
example : (degreeVectors 0 0).length = 1 := by decide
example : (degreeVectors 0 1).length = 0 := by decide

#print axioms vectors_toFinset
#print axioms sum_vectors
#print axioms eval_sum_vectors
end NewDegreeEnumeration
