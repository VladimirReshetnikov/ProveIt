import DirectBFSModelMass
import Mathlib.Tactic.Linarith
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option exponentiation.threshold 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DirectBFSKernelLowerBound
open scoped BigOperators
open DirectBFSSymbolicKernel DirectBFSModelMass DirectBFSCoefficientMass

def lower (r : ℕ) : ℕ :=
  r^30+r^62+r^1100+r^2201 +
    (∑ i : Fin 943, selectors i*(r^(4393-i.val)+r^(5495-i.val))) +
    (∑ i : Fin 41, copies i*(r^(4393-CompactSymbolicKernel.position i)+r^(5495-CompactSymbolicKernel.position i)))

theorem kernel_split (r : ℕ) : paramKernel r=lower r+r^8807*r^42 := by rfl

theorem lower_lt (r : ℕ) (hr : 2^67≤r) : lower r < r^5496 := by
  have hrpos : 0<r := by
    have h : 0<2^67 := by norm_num
    omega
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
    unfold lower
    nlinarith
  have hm : 2*selectorMass+2*copyMass+4<r := by
    rw [selector_mass_exact,copy_mass_exact]
    have hnum : 2*12777109108488111+2*2251799813684224+4<2^67 := by decide
    omega
  have hP : 0<P := pow_pos hrpos _
  calc
    lower r ≤ (2*selectorMass+2*copyMass+4)*P := hk
    _ < r*P := Nat.mul_lt_mul_of_pos_right hm hP
    _ = r^5496 := by
      change r*r^5495=r^5496
      have he := (pow_succ r 5495).symm
      simpa only [Nat.reduceAdd,Nat.mul_comm] using he
#print axioms DirectBFSKernelLowerBound.kernel_split
#print axioms DirectBFSKernelLowerBound.lower_lt
end DirectBFSKernelLowerBound
