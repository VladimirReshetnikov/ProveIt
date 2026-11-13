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
  4 + B * (B^1012 * (1 * (∑ j ∈ range 10, B^j) + B^10 * (B^42 * (1 * (∑ j ∈ range 9, B^j) + B^9 * (B^1121 * (1 + B * (B^1100 * (1 + B * (B^1096 * (a + B * (B^1101 * (a + B * (B^3296 * (b * (∑ j ∈ range 13, B^j) + B^13 * (c + B * (0 + B * (0))))))))))))))))) := by
  simp only [runs, Nat.ofDigits_append, Nat.ofDigits_singleton,
    Nat.ofDigits_replicate_zero, List.length_singleton, List.length_replicate,
    replicate_value, Nat.ofDigits_cons, Nat.ofDigits_nil, pow_one,
    zero_mul, mul_zero, add_zero, zero_add, one_mul]

#print axioms BFSHighRuns.expansion
end BFSHighRuns
