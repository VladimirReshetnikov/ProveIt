import DiophantineConsistency.Source34.Source34Kernel
import DiophantineConsistency.Mixed121.Mixed121KernelResidue

/-! # The source34 kernel modulo the controller modulus

`paramKernel (2^121) ≡ 2050743806 (mod C0)`, where `C0 = d·λ = 2492980061`.
This is the residue premise of `Source34ConstructionUnit.gamma_unit`.

The design is `Mixed121KernelResidue`'s: the 943 clause coefficients, which
are the same as at 121x8801, are folded by Horner's rule in `ZMod C0`
(`Mixed121KernelResidue.evaluate`, `clause_reflection`); the 44 stride-two
copy and anchor weights are a separate sum (`copies_common`); `2^121 mod C0`
is `reduce_mod_char`. The residue agrees with the pinned source34 payload
`K0.bin`, recomputed from its bytes. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace Source34KernelResidue
open Source34Kernel
open Mixed121Kernel (W clause rho)
open Mixed121KernelResidue (evaluate evaluate_eq_run clause_reflection Modulus Radix)
open scoped BigOperators

def copyReflection {R : Type*} [CommSemiring R] (r : R) : R :=
  ∑ k : Fin 44, ((W k.val : ℕ) : R) * (r^(4393-extraPos k) + r^(5495-extraPos k))

private theorem rows_common : evaluate (Radix : ZMod Modulus) Compact943Data.rows =
    2093779003 := by
  rw [evaluate_eq_run]
  decide +kernel

private theorem copies_common : copyReflection (Radix : ZMod Modulus) = 972974519 := by
  decide +kernel

private theorem rho_common : (rho : ZMod Modulus) = Radix := by
  change (2 : ZMod Modulus)^121 = Radix
  reduce_mod_char

theorem kernel_cast : (paramKernel rho : ZMod Modulus) = 2050743806 := by
  rw [paramKernel]
  simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  change ((rho : ZMod Modulus)^40 + (rho : ZMod Modulus)^41 +
      (rho : ZMod Modulus)^1100 + (rho : ZMod Modulus)^2200 +
      (∑ i : Fin 943, (clause (Compact943Data.row i) : ZMod Modulus) *
        ((rho : ZMod Modulus)^(4393-i.val) + (rho : ZMod Modulus)^(5495-i.val))) +
      copyReflection (rho : ZMod Modulus) + (rho : ZMod Modulus)^8801 *
        (rho : ZMod Modulus)^1) = 2050743806
  rw [clause_reflection, rho_common, rows_common, copies_common]
  reduce_mod_char

theorem kernel_mod : paramKernel rho % Modulus = 2050743806 := by
  have h := congrArg ZMod.val kernel_cast
  have hr : (2050743806 : ZMod Modulus).val = 2050743806 := by decide +kernel
  simpa only [ZMod.val_natCast, hr] using h

#print axioms kernel_cast
#print axioms kernel_mod
end Source34KernelResidue
