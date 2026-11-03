import BFSHighGeneric

/-! Expand the complete high-digit run shape at a symbolic radix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace BFSHighRuns
open Finset BFSHighGeneric
open scoped BigOperators

def runs (a b c : ℕ) : List ℕ :=
  [4] ++ List.replicate 1012 0 ++ List.replicate 10 1 ++
  List.replicate 42 0 ++ List.replicate 9 1 ++
  List.replicate 1121 0 ++ [1] ++ List.replicate 1100 0 ++ [1] ++
  List.replicate 1096 0 ++ [a] ++ List.replicate 1101 0 ++ [a] ++
  List.replicate 3296 0 ++ List.replicate 13 b ++ [c,0]

theorem expansion (B a b c : ℕ) : Nat.ofDigits B (runs a b c) =
    4 + B^1013 * (∑ j ∈ range 10, B^j) + B^1065 * (∑ j ∈ range 9, B^j) +
    B^2195 + B^3296 + B^4393*a + B^5495*a +
    B^8792 * (b * (∑ j ∈ range 13, B^j)) + B^8805*c := by
  simp only [runs, Nat.ofDigits_append, List.length_append, List.length_cons,
    List.length_nil, List.length_replicate, replicate_value, Nat.ofDigits_cons,
    Nat.ofDigits_nil, pow_one, zero_mul, mul_zero, add_zero, one_mul, mul_one,
    Nat.reduceAdd]

#print axioms BFSHighRuns.expansion
end BFSHighRuns
