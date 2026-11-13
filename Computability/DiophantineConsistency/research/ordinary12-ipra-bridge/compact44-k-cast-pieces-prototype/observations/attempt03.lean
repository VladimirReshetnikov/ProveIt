import DiophantineConsistency.TwoBand
import DiophantineConsistency.CompactSymbolicKernelOpaque
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace KCast
open DiophantineConsistency CompactSymbolicKernel CompactSymbolicKernelOpaque
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] rho

theorem cast_rho_pow (e : ℕ) :
    ((rho : ℕ) : V)^e = Exp.exp ((67 : V) * (e : V)) := by
  calc
    ((rho : ℕ) : V)^e = (((2^67 : ℕ)^e : ℕ) : V) := by rw [← Nat.cast_pow, rho]
    _ = ((2^(67*e) : ℕ) : V) := by rw [pow_mul]
    _ = Exp.exp ((67 : V) * (e : V)) := by
      rw [← ArithmeticStandardCasts.cast_exp (V:=V) (67*e)]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
#print axioms KCast.cast_rho_pow
end KCast
