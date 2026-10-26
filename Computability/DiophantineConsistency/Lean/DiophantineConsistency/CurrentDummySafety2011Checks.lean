import DiophantineConsistency.CurrentDummySafety2011

namespace DiophantineConsistency.CurrentDummySafety2011Checks

open CurrentMasks2011 CurrentDummySafety2011 CurrentDummyMutation2011
  CurrentWordConstruction2011 CurrentWordClause2011

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local irreducible] CurrentKernel2011.K

-- The spatial term is the true maximum exponent; it cannot be omitted.
example : CurrentKernel2011.exponent (.inl (2 : Fin 3)) = 2020 := rfl
example : ¬CurrentKernel2011.exponent (.inl (2 : Fin 3)) ≤ 1005 := by decide
example : CurrentKernel2011.K < radix^2022 := kernel_upper_bound

-- Zero stride and coincident next/temporal cells are both covered.
example : (CurrentKernel2011.K+2^(displacement 0))*dummyIncrement (0 : ZMod 2) <
    radix^(2*2011-2) := (safe_increment_bound 0 0 (by decide) (by decide)).2
example : (CurrentKernel2011.K+2^(displacement 1))*dummyIncrement (0 : ZMod 2) <
    radix^(2*2011-2) := (safe_increment_bound 1 0 (by decide) (by decide)).2

-- Canonical representatives matter even for repeated integer cell casts.
example : (CurrentKernel2011.K+2^(displacement 1))*dummyIncrement (6 : ZMod 3) <
    radix^(3*2011)/radix^2 := safe_increment_div_bound 1 6 (by decide) (by decide)
example : (CurrentKernel2011.K+2^(displacement 1))*dummyIncrement (1 : ZMod 3) <
    radix^(3*2011)/radix^2 := safe_increment_div_bound 1 1 (by decide) (by decide)

-- No safe dummy exists at N=1; this is not an unmentioned size premise.
example (j : ZMod 1) : ¬j.val+1 < 1 := by omega
example {N : ℕ} (j : ZMod N) (hj : j.val+1 = N) : ¬j.val+1 < N := by omega

-- A last-cell source places the literal spatial contribution beyond the
-- whole word; a temporal destination equal to N likewise does not fit.
example {N : ℕ} (j : ZMod N) (hj : j.val+1 = N) :
    N*2011 ≤ 2020+977+2011*j.val := by omega
example {N : ℕ} (j : ZMod N) (s : ℕ) (hj : j.val+s = N) :
    N*2011 ≤ 977+2011*(j.val+s) := by omega
example : (0 : ZMod 3).val+1 < 3 ∧ ¬(0 : ZMod 3).val+3 < 3 := by decide

-- Construct both normalizations from an arbitrary actual two-cell tile
-- assignment and arbitrary Boolean marker controls. No matching, marked
-- origin, high mask, old F, or desired increment is assumed.
example (a : ZMod 2 → Fin 942) (marker : ZMod 2 → ℕ)
    (hm : ∀ j, marker j ≤ 1) :
    ∃ k f k' f' : ZMod (2*2011) → ℕ,
      CurrentCarryConstruction2011.Facts (word a (fun _ => 0) marker)
        (displacement 0) k f ∧
      CurrentCarryConstruction2011.Facts
        (word a (Function.update (fun _ => 0) 0 1) marker) (displacement 0) k' f' ∧
      NativeCyclicConvolution.word radix
          (word a (Function.update (fun _ => 0) 0 1) marker) =
        NativeCyclicConvolution.word radix (word a (fun _ => 0) marker)+
          dummyIncrement (0 : ZMod 2) ∧
      NativeCyclicConvolution.word radix f' = NativeCyclicConvolution.word radix f+
        (CurrentKernel2011.K+2^(displacement 0))*dummyIncrement (0 : ZMod 2) := by
  obtain ⟨k,f,hf⟩ := CurrentCarryConstruction2011.exists_assembled_normalization
    a (fun _ => 0) marker (by intro; decide) hm (displacement 0)
  obtain ⟨k',f',hf',hC,hF⟩ := exists_safe_normalized_increment
    a (fun _ => 0) marker (by intro; decide) hm 0 0 rfl
    (by decide) (by decide) k f hf
  exact ⟨k,f,k',f',hf,hf',hC,hF⟩

-- Enabling an already enabled dummy remains excluded by the update theorem.
example : ¬(fun _ : ZMod 2 => (1 : ℕ)) 0 = 0 := by decide

#print axioms kernel_exponent_le
#print axioms kernel_upper_bound
#print axioms displacement_power
#print axioms dummyIncrement_power
#print axioms temporal_dummy_power
#print axioms kernel_dummy_bound
#print axioms safe_exponent_bounds
#print axioms safe_increment_bound
#print axioms safe_increment_div_bound
#print axioms normalized_nonwrap_of_safe
#print axioms safe_normalized_increment
#print axioms exists_safe_normalized_increment
#print axioms safe_rank_decrement

end DiophantineConsistency.CurrentDummySafety2011Checks
