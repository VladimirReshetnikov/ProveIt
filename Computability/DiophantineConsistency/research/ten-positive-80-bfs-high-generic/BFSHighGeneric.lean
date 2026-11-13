import DiophantineConsistency.CompactConcreteMask
import DiophantineConsistency.CompactHighPopulation

/-! Expanding constant radix runs without evaluating the radix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace BFSHighGeneric
open Finset
open scoped BigOperators

theorem replicate_value (B n d : ℕ) :
    Nat.ofDigits B (List.replicate n d) = d * (∑ j ∈ range n, B^j) := by
  have h := CompactListMask.ofDigits_map_range B (fun _ => d) n
  simpa only [List.map_const', List.length_range, Finset.mul_sum] using h

theorem run_sum (B n d : ℕ) (xs : List ℕ) :
    Nat.ofDigits B (List.replicate n d ++ xs) =
      d * (∑ j ∈ range n, B^j) + B^n * Nat.ofDigits B xs := by
  rw [Nat.ofDigits_append, List.length_replicate, replicate_value]

#print axioms BFSHighGeneric.replicate_value
#print axioms BFSHighGeneric.run_sum
end BFSHighGeneric
