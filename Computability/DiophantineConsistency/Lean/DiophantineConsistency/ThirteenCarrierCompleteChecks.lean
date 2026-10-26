import DiophantineConsistency.ThirteenCarrierComplete

/-! Literal coordinate checks and a finite control for the extra low-mask residue. -/

open DiophantineConsistency DiophantineConsistency.ThirteenCarrierComplete

-- The new i is chosen afresh; the outer first-root carrier n is retained exactly.
example (v : Fin 14 → ℤ) (f i T m : ℤ) : replace v f i T m 4 = i := rfl
example (v : Fin 14 → ℤ) (f i T m : ℤ) : replace v f i T m 8 = v 9 := rfl
example (v : Fin 14 → ℤ) (f i T m : ℤ) : replace v f i T m 11 = m := rfl
example (v : Fin 14 → ℤ) (f i T m : ℤ) : SameOuter v (replace v f i T m) :=
  replace_same_outer v f i T m

example (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) (f i T m : ℤ) :
    (ThirteenCarrier.core p (replace v f i T m)).P = (Carrier65.core p v).P ∧
      (ThirteenCarrier.core p (replace v f i T m)).Q = (Carrier65.core p v).Q := ⟨rfl,rfl⟩

-- This finite tuple satisfies BOTH coefficient interfaces, but MC%4 is zero.
-- It controls the added premise only; it asserts no polynomial solution.
private def controlPorts : Fin 4 → ℤ := ![31,1,24,59]

example : Carrier65Witness.PortBounds controlPorts := by
  constructor <;> decide +kernel

example : NativeSourceMask.Interface controlPorts 5 24 28 := by
  constructor <;> decide +kernel

example : (24 : ℕ) % 4 ≠ 2 := by decide

#print axioms source_rank_mod_four
#print axioms source_spatial_gt_base
#print axioms outer_facts
#print axioms core_replace
#print axioms replace_zero69
#print axioms positive_zero_completes
#print axioms polynomial_zero_completes
