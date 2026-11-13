import DiophantineConsistency.Compact44.TwoBand
import DiophantineConsistency.Compact44.CompactSymbolicKernelOpaque
import Mathlib.Algebra.BigOperators.Fin
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
theorem bare_formula :
    TwoBand.bareKernel (V:=V) =
      Exp.exp (67*(30:V)) + Exp.exp (67*(62:V)) + Exp.exp (67*(1100:V)) +
      Exp.exp (67*(2201:V)) + Exp.exp (67*(8849:V)) := by
  unfold TwoBand.bareKernel TwoBand.bareOffset
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Nat.cast_ofNat, add_zero]
  ring
#print axioms KCast.cast_rho_pow
#print axioms KCast.bare_formula
end KCast
