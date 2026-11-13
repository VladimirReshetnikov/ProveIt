import DiophantineConsistency.CompactSymbolicPorts
import DiophantineConsistency.CompactConcreteMask
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74HighDigitBound
open Finset CompactListMask CompactConcreteMask CompactHighPopulation
open CompactSymbolicPorts
open scoped BigOperators
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
def B : ℕ := 2^67
def highPrefix : List ℕ :=
  [4] ++ List.replicate 1012 0 ++ List.replicate 10 1 ++
  List.replicate 42 0 ++ List.replicate 9 1 ++
  List.replicate 1121 0 ++ [1] ++ List.replicate 1100 0 ++ [1] ++
  List.replicate 1096 0
def highTail : List ℕ :=
  List.replicate 1101 0 ++ [mu] ++ List.replicate 3296 0 ++
  List.replicate 13 padding ++ [lastPadding,0]
def suffix : List ℕ := mu :: highTail

theorem high_split : highDigits=highPrefix++suffix := by
  simp only [highDigits,highPrefix,suffix,highTail,List.singleton_append,List.append_assoc]

theorem prefix_length : highPrefix.length=4393 := by
  simp only [highPrefix,List.length_append,List.length_replicate,List.length_cons,List.length_nil]

theorem high_at_least : B^4393 ≤ highNat := by
  have hsuf : 1≤Nat.ofDigits B suffix := by
    change 1 ≤ Nat.ofDigits B (mu :: highTail)
    rw [Nat.ofDigits_cons]
    have hm : 1≤mu := by norm_num [mu]
    exact le_trans hm (Nat.le_add_right _ _)
  have hp : B^4393 ≤ B^4393 * Nat.ofDigits B suffix :=
    Nat.le_mul_of_pos_right _ hsuf
  change B^4393 ≤ Nat.ofDigits B highDigits
  rw [high_split,Nat.ofDigits_append,prefix_length]
  omega


#print axioms Trace74HighDigitBound.high_at_least
end Trace74HighDigitBound
