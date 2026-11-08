import DiophantineConsistency.BFS943.DirectBFSSymbolicKernel
import Mathlib.Algebra.BigOperators.Ring.Finset
import DiophantineConsistency.ArithmeticModularCancellation
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSKernelDivisibility
open scoped BigOperators
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticStandardCasts

theorem radix_dvd (r : ℕ) : r ∣ DirectBFSSymbolicKernel.paramKernel r := by
  have hp (n : ℕ) (hn : 0<n) : r ∣ r^n := dvd_pow_self r (Nat.ne_of_gt hn)
  have hs : r ∣ ∑ i : Fin 943, CompactCoefficientMass.selector (DirectBFSSymbolicKernel.row i)*
      (r^(4393-i.val)+r^(5495-i.val)) := by
    apply Finset.dvd_sum
    intro i _
    apply dvd_mul_of_dvd_right
    apply Nat.dvd_add <;> apply hp <;> have hi := i.isLt <;> omega
  have hc : r ∣ ∑ i : Fin 41, (2^(10+i.val):ℕ)*
      (r^(4393-CompactSymbolicKernel.position i)+r^(5495-CompactSymbolicKernel.position i)) := by
    apply Finset.dvd_sum
    intro i _
    apply dvd_mul_of_dvd_right
    apply Nat.dvd_add <;> apply hp <;> have hi := CompactSymbolicKernel.position_lt_target i <;> omega
  unfold DirectBFSSymbolicKernel.paramKernel
  exact Nat.dvd_add (Nat.dvd_add (Nat.dvd_add (Nat.dvd_add (Nat.dvd_add (Nat.dvd_add (hp 30 (by decide)) (hp 62 (by decide)))
    (hp 1100 (by decide))) (hp 2201 (by decide))) hs) hc) (dvd_mul_of_dvd_left (hp 8807 (by decide)) _)

theorem kernel_dvd_four : 4 ∣ DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho := by
  have h : 4 ∣ CompactSymbolicKernel.rho := by unfold CompactSymbolicKernel.rho; norm_num
  exact dvd_trans h (radix_dvd _)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem kernel_model_dvd_four : (4:V) ∣ ((DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho:ℕ):V) := by
  have hn : DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho%4=0 := Nat.mod_eq_zero_of_dvd kernel_dvd_four
  have h := cast_mod (V:=V) (DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho) 4
  rw [hn] at h
  apply mod_eq_zero_iff_dvd.mp
  simpa using h.symm
#print axioms DirectBFSKernelDivisibility.radix_dvd
#print axioms DirectBFSKernelDivisibility.kernel_dvd_four
#print axioms DirectBFSKernelDivisibility.kernel_model_dvd_four
end DirectBFSKernelDivisibility
