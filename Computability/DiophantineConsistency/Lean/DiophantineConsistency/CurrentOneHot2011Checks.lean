import DiophantineConsistency.CurrentOneHot2011

namespace DiophantineConsistency.CurrentOneHot2011Checks

open CurrentOneHot2011 CurrentPolynomialWindow2011 CurrentWindowCarry2011
  NativeCyclicRotation NativeBooleanRotation
open scoped BigOperators

set_option Elab.async false

-- The final endpoint starts with only the actual positive polynomial zero.
example (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v (Carrier65.polynomial ports) = 0) :
    ∃ N, ∃ hN : 0 < N, CountPhaseWindow v N hN :=
  polynomial_zero_count_phase v hv hz

-- The forced origin is occupied exactly once; other cells are still allowed empty.
example {N : ℕ} [NeZero (N * 2011)] (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits) :
    (∑ f : Fin 942, c (f.val : ZMod (N * 2011))) = 1 := by
  have hu := (facts_count_phase v x c carry digits h).1 0 (by simp)
  simp only [zero_add] at hu
  have hl := Finset.single_le_sum
    (fun f (_ : f ∈ (Finset.univ : Finset (Fin 942))) =>
      Nat.zero_le (c (f.val : ZMod (N * 2011)))) (Finset.mem_univ (0 : Fin 942))
  simp only [Fin.val_zero, Nat.cast_zero, h.origin] at hl
  omega

-- Only fractional phase is removed: the whole-field shift remains explicit.
example {N : ℕ} [NeZero (N * 2011)] (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits)
    (i : ZMod (N * 2011)) :
    binaryRotation 47 ((Carrier65.core ports v).rank.toNat - 47 * (N * 2011)) c i =
      c (i - ((((Carrier65.core ports v).rank.toNat - 47 * (N * 2011)) / 47 : ℕ) :
        ZMod (N * 2011))) :=
  rotation_zero_phase (by decide) _ c h.boolean (facts_count_phase v x c carry digits h).2 i

#print axioms literal_count_le_one
#print axioms physical_count_le_one
#print axioms facts_count_phase
#print axioms polynomial_zero_count_phase

end DiophantineConsistency.CurrentOneHot2011Checks
