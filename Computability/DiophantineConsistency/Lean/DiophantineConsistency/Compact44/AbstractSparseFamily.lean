import DiophantineConsistency.Compact44.SparseRadix
import Mathlib.Algebra.BigOperators.Fin

open Finset
namespace AbstractSparseFamily

def terms {n : ℕ} (position weight : Fin n → ℕ) : List (ℕ × ℕ) :=
  List.ofFn (fun i => (position i, weight i))

theorem weighted_sum {n : ℕ} (r : ℕ) (position weight : Fin n → ℕ) :
    ((terms position weight).map (fun t => t.2 * r ^ t.1)).sum =
      ∑ i : Fin n, weight i * r ^ position i := by
  simp [terms, List.map_ofFn, List.sum_ofFn]

def twoBands {n : ℕ} (left right weight : Fin n → ℕ) : List (ℕ × ℕ) :=
  terms left weight ++ terms right weight

theorem twoBands_weighted_sum {n : ℕ} (r : ℕ) (left right weight : Fin n → ℕ) :
    ((twoBands left right weight).map (fun t => t.2 * r ^ t.1)).sum =
      ∑ i : Fin n, weight i * (r ^ left i + r ^ right i) := by
  simp only [twoBands, List.map_append, List.sum_append, weighted_sum,
    mul_add, Finset.sum_add_distrib]

#print axioms AbstractSparseFamily.weighted_sum
#print axioms AbstractSparseFamily.twoBands_weighted_sum
end AbstractSparseFamily
