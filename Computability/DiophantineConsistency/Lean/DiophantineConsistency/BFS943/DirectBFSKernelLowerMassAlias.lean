import DiophantineConsistency.BFS943.DirectBFSKernelLowerBound
import DiophantineConsistency.BFS943.DirectBFSModelMass
import Mathlib.Tactic.Linarith
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option exponentiation.threshold 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DirectBFSKernelLowerMassAlias
open scoped BigOperators
open DirectBFSSymbolicKernel DirectBFSModelMass DirectBFSCoefficientMass

abbrev lower (r : ℕ) : ℕ := DirectBFSKernelLowerBound.lower r

theorem kernel_split (r : ℕ) : paramKernel r=lower r+r^8807*r^42 :=
  DirectBFSKernelLowerBound.kernel_split r

theorem lower_le (r : ℕ) (hr : 1≤r) : lower r ≤ 2^62*r^5495 := by
  have hrpos : 0<r := by omega
  let P := r^5495
  have hpow (n : ℕ) (hn : n≤5495) : r^n≤P := Nat.pow_le_pow_right hrpos hn
  have hbare : r^30+r^62+r^1100+r^2201≤4*P := by
    have h1 := hpow 30 (by omega)
    have h2 := hpow 62 (by omega)
    have h3 := hpow 1100 (by omega)
    have h4 := hpow 2201 (by omega)
    omega
  have hs : (∑ i : Fin 943, selectors i*(r^(4393-i.val)+r^(5495-i.val))) ≤ selectorMass*(2*P) := by
    calc
      _ ≤ ∑ i : Fin 943, selectors i*(2*P) := by
        apply Finset.sum_le_sum
        intro i _
        apply Nat.mul_le_mul_left
        have h1 := hpow (4393-i.val) (by omega)
        have h2 := hpow (5495-i.val) (by omega)
        omega
      _ = selectorMass*(2*P) := by rw [←Finset.sum_mul,selectors_mass]
  have hc : (∑ i : Fin 41, copies i*(r^(4393-CompactSymbolicKernel.position i)+r^(5495-CompactSymbolicKernel.position i))) ≤ copyMass*(2*P) := by
    calc
      _ ≤ ∑ i : Fin 41, copies i*(2*P) := by
        apply Finset.sum_le_sum
        intro i _
        apply Nat.mul_le_mul_left
        have h1 := hpow (4393-CompactSymbolicKernel.position i) (by omega)
        have h2 := hpow (5495-CompactSymbolicKernel.position i) (by omega)
        omega
      _ = copyMass*(2*P) := by rw [←Finset.sum_mul,copies_mass]
  have hk : lower r≤(2*selectorMass+2*copyMass+4)*P := by
    unfold lower DirectBFSKernelLowerBound.lower
    nlinarith
  have hm : 2*selectorMass+2*copyMass+4≤2^62 := by
    rw [selector_mass_exact,copy_mass_exact]
    decide
  calc
    lower r ≤ (2*selectorMass+2*copyMass+4)*P := hk
    _ ≤ 2^62*P := Nat.mul_le_mul_right P hm
    _ = 2^62*r^5495 := rfl
#print axioms DirectBFSKernelLowerMassAlias.kernel_split
#print axioms DirectBFSKernelLowerMassAlias.lower_le
end DirectBFSKernelLowerMassAlias
