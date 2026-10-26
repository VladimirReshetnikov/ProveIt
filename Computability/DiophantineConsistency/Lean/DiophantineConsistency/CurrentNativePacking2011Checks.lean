import DiophantineConsistency.CurrentNativePacking2011

namespace DiophantineConsistency.CurrentNativePacking2011Checks

open CurrentNativePacking2011 CurrentWordScalarWitness2011
  CurrentWordConstruction2011 CurrentWordCopies2011
  NativeCyclicConvolution CurrentMasks2011 WangTiles942Periodic

set_option Elab.async false

-- The literal repunit includes its origin term even at the smallest window.
example : NativeMaskPopulation.repunit width 1 = 1 := by
  rw [NativeSourceMask.repunit_eq_geom]
  simp

-- The equation is ordinary natural arithmetic, without modular reduction.
example : beta*NativeMaskPopulation.repunit width 2+1 = q 2 := repunit_balance

-- Carries, F, alpha, z and both masks are constructed for the same word.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942)
    (dummy : ZMod N → ℕ) (hd : ∀ j, dummy j ≤ 1) (s : ℕ)
    (ha : MarkedWord N (s : ℤ) a) :
    ∃ k digits : ZMod (N*2011) → ℕ,
      Facts a dummy s k digits ∧
      0 < normalized digits ∧
      word radix digits &&& (highPort*NativeMaskPopulation.repunit width N-1) = 0 := by
  obtain ⟨k,digits,h⟩ := marked_constructs_packing a dummy hd s ha
  exact ⟨k,digits,h,h.scalars.normalized_pos,h.high_mask⟩

-- The second control can be uniformly enabled; no requested mask is assumed.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (s : ℕ)
    (ha : MarkedWord N (s : ℤ) a) :
    ∃ k digits : ZMod (N*2011) → ℕ, Facts a (fun _ => 1) s k digits :=
  marked_constructs_packing a (fun _ => 1) (fun _ => by omega) s ha

-- A halt supplies a unique-Start word at independently large actual powers.
example (p : ℕ) (hp : 1 < p) (T wBound hBound : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none) :
    ∃ rw rh : ℕ, 0 < rw ∧ 0 < rh ∧ wBound < p^rw ∧ hBound < p^rh ∧
      p^rw*p^rh = p^(rw+rh) ∧
      letI : NeZero (p^rw*p^rh) := ⟨Nat.mul_ne_zero
        (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by omega))⟩
      ∃ a : ZMod (p^rw*p^rh) → Fin 942,
      ∃ k digits : ZMod ((p^rw*p^rh)*2011) → ℕ,
        MarkedWord (p^rw*p^rh) ((p^rw : ℕ) : ℤ) a ∧
        (∀ z, a z = 0 ↔ z = 0) ∧ Facts a (fun _ => 0) (p^rw) k digits :=
  halt_constructs_power_packing p hp T wBound hBound hh

#print axioms repunit_pos
#print axioms repunit_balance
#print axioms marked_constructs_packing
#print axioms halt_constructs_power_packing

end DiophantineConsistency.CurrentNativePacking2011Checks
