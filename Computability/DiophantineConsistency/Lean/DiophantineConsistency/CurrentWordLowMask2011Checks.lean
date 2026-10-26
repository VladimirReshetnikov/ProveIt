import DiophantineConsistency.CurrentWordLowMask2011

namespace DiophantineConsistency.CurrentWordLowMask2011Checks

open CurrentWordLowMask2011 CurrentMasks2011 NativeCyclicConvolution
  NativeRadixDigits CurrentSparseDigits2011

set_option Elab.async false

-- The origin increment is used even in the one-position cyclic group.
example : (word 2 (fun _ : ZMod 1 => 1)-1) &&&
    word 2 (originMask 2 (fun _ : ZMod 1 => 1)) = 0 :=
  encode_originMask (v := 1) (by decide) (fun _ => 1) (fun _ => 1)
    (fun _ => by omega) (fun _ => by decide) rfl

-- Without subtracting the Start unit, the literal origin mask rejects it.
example : word 2 (fun _ : ZMod 1 => 1) &&&
    word 2 (originMask 2 (fun _ : ZMod 1 => 1)) ≠ 0 := by decide

-- Mixed capacities are retained, including a forbidden nonorigin digit.
example {n : ℕ} [NeZero n] (c bits : ZMod n → ℕ)
    (hb : ∀ k, bits k ≤ 47) (hc : ∀ k, c k < 2^bits k) (h0 : c 0 = 1) :
    (word (2^47) c-1) &&& word (2^47) (originMask (2^47) bits) = 0 :=
  encode_originMask (v := 47) (by decide) c bits hb hc h0

-- Independent all-one controls are allowed. The single-cell edge case
-- binds the actual low port and its full +1 origin increment.
example (a : ZMod 1 → Fin 942) (ha : a 0 = 0) :
    (word radix (CurrentWordConstruction2011.word a (fun _ => 1) (fun _ => 1))-1) &&&
      (lowPort*NativeMaskPopulation.repunit width 1+1) = 0 :=
  assembled_low_mask a _ _ (fun _ => by omega) (fun _ => by omega) ha

-- No carry/transport/matching premise occurs in the complete scalar result.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (ha : a 0 = 0) :
    let C := word radix (CurrentWordConstruction2011.word a dummy marker)
    0 < C ∧ C < radix^(N*2011) ∧
      (C-1) &&& (lowPort*NativeMaskPopulation.repunit width N+1) = 0 :=
  ⟨(assembled_source_bounds a dummy marker hd hm ha).1,
    (assembled_source_bounds a dummy marker hd hm ha).2,
    assembled_low_mask a dummy marker hd hm ha⟩

#print axioms encode_originMask
#print axioms assembled_capacity
#print axioms assembled_low_mask
#print axioms assembled_source_bounds

end DiophantineConsistency.CurrentWordLowMask2011Checks
