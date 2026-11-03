import DiophantineConsistency.CompactFixedBeta
import DiophantineConsistency.CompactSymbolicPorts
import DiophantineConsistency.CompactConcreteMask

/-! UNCHECKED DRAFT. A non-expanding proof of the actual symbolic mask cover.
The low-mask defect has only 3297 base-2^67 digits; the high mask contains
an explicitly positive digit at position 4393. No graph or no-carry theorem
is asserted here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74SymbolicFixedMaskCover
open Finset CompactListMask CompactConcreteMask CompactHighPopulation
open CompactFixedBeta CompactSymbolicPorts
open scoped BigOperators
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic

def B : ℕ := 2^67
def smallDefect : List ℕ := (List.range 3297).map (defect 1063 support)
def prefix : List ℕ :=
  [4] ++ List.replicate 1012 0 ++ List.replicate 10 1 ++
  List.replicate 42 0 ++ List.replicate 9 1 ++
  List.replicate 1121 0 ++ [1] ++ List.replicate 1100 0 ++ [1] ++
  List.replicate 1096 0
def suffix : List ℕ :=
  [mu] ++ List.replicate 1101 0 ++ [mu] ++ List.replicate 3296 0 ++
  List.replicate 13 padding ++ [lastPadding,0]

theorem support_short : support ⊆ Finset.range 3297 := by
  intro j hj
  simp only [support, Finset.mem_sdiff, Finset.mem_union, Finset.mem_range,
    Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton] at hj ⊢
  omega

theorem defect_sum_short :
    (∑ j ∈ Finset.range 3297, defect 1063 support j * B^j) =
    ∑ j ∈ Finset.range 8807, defect 1063 support j * B^j := by
  apply Finset.sum_subset (Finset.range_mono (by decide : 3297≤8807))
  intro j _ hj
  have hge : 3297≤j := by simpa only [Finset.mem_range,not_lt] using hj
  have hs : j∉support := by
    intro hm
    have hm' := support_short hm
    simp only [Finset.mem_range] at hm'
    omega
  have hn : j≠1063 := by omega
  simp [defect,hn,hs]

theorem low_plus_defect : lowNat + Nat.ofDigits B smallDefect + 1 = B^8807 := by
  have h := digits_add_defect B 8807 1063 support (by norm_num [B])
  rw [← defect_sum_short, ← ofDigits_map_range B (defect 1063 support) 3297] at h
  exact h

theorem defect_lt : Nat.ofDigits B smallDefect < B^3297 := by
  have hd : ∀ x ∈ smallDefect, x<B := by
    intro x hx
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
    unfold defect
    split_ifs <;> norm_num [B]
  have h := Nat.ofDigits_lt_base_pow_length (show 1<B by norm_num [B]) hd
  simpa only [smallDefect,List.length_map,List.length_range] using h

theorem high_split : highDigits=prefix++suffix := by
  simp only [highDigits,prefix,suffix,List.append_assoc]

theorem prefix_length : prefix.length=4393 := by
  simp only [prefix,List.length_append,List.length_replicate,List.length_cons,List.length_nil]

theorem high_at_least : B^4393 ≤ highNat := by
  have hsuf : 1≤Nat.ofDigits B suffix := by
    simp only [suffix,List.singleton_append,Nat.ofDigits_cons]
    have hm : 1≤mu := by norm_num [mu]
    omega
  have hp : B^4393 ≤ B^4393 * Nat.ofDigits B suffix :=
    Nat.le_mul_of_pos_right _ hsuf
  change B^4393 ≤ Nat.ofDigits B highDigits
  rw [high_split,Nat.ofDigits_append,prefix_length]
  omega

theorem cover_nat : betaNat+1≤lowNat+highNat := by
  have hbeta : betaNat+1=B^8807 := by
    unfold betaNat B
    rw [Nat.sub_add_cancel (Nat.one_le_two_pow (n:=67*8807)),←pow_mul]
  have hpow : B^3297≤B^4393 :=
    Nat.pow_le_pow_right (show 0<B by norm_num [B]) (by decide)
  have hdef : Nat.ofDigits B smallDefect < highNat :=
    lt_of_lt_of_le defect_lt (le_trans hpow high_at_least)
  calc
    betaNat+1 = B^8807 := hbeta
    _ = lowNat + Nat.ofDigits B smallDefect + 1 := low_plus_defect.symm
    _ = lowNat + (Nat.ofDigits B smallDefect + 1) := by rw [Nat.add_assoc]
    _ ≤ lowNat + highNat := Nat.add_le_add_left (Nat.succ_le_of_lt hdef) lowNat

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cover_model : (betaNat:V)+1 ≤ (lowNat:V)+(highNat:V) := by
  have h := (Nat.cast_le.mpr cover_nat : ((betaNat+1:ℕ):V)≤((lowNat+highNat:ℕ):V))
  simpa only [Nat.cast_add,Nat.cast_one] using h
end Model

#print axioms Trace74SymbolicFixedMaskCover.cover_nat
#print axioms Trace74SymbolicFixedMaskCover.cover_model
end Trace74SymbolicFixedMaskCover
